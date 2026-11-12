//! The order of admissions in one environment does not change a verdict.
//!
//! The environment keeps the outcomes of its admissions across declarations.
//! A formation that a refused declaration kept owes obligations that its drain
//! refused, so a later declaration that recalls the formation must check them
//! again.

use gandr_kernel_core::Environment;
use gandr_kernel_core::KernelError;
use gandr_kernel_strata::Level;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::LevelSignature;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::ValueTypeId;

/// The obligation that the declared type's formation owes.
#[derive(Clone, Copy, Debug)]
enum Kind
{
    Endpoints,
    Universe,
    Data,
    Codata,
}

/// The form of the declaration.
#[derive(Clone, Copy, Debug)]
enum Form
{
    Axiom,
    Definition,
}

/// Whether the owed obligation holds.
#[derive(Clone, Copy, Debug)]
enum Owes
{
    Holds,
    Fails,
}

const KINDS: [Kind; 4] = [Kind::Endpoints, Kind::Universe, Kind::Data, Kind::Codata];

/// Admit a data family and a codata family, each over one code of the
/// universe at level zero.
///
/// # Specification
/// trivial.
fn families(environment: &mut Environment) -> (ConstantIndex, ConstantIndex)
{
    let mut staging = environment.stage();
    let universe = staging
        .arena()
        .value_type_universe(GroundSort::Value, Level::zero());
    let declaration = staging.data(
        LevelSignature::monomorphic(),
        vec![universe],
        vec![],
        universe,
    );
    let data = environment
        .add_decl(declaration)
        .expect("a data family over one code")
        .position();
    let mut staging = environment.stage();
    let arena = staging.arena();
    let universe = arena.value_type_universe(GroundSort::Value, Level::zero());
    let parameter = arena.value_variable(DeBruijnIndex::from(0));
    let element = arena.value_type_element(parameter, Level::zero());
    let head = arena.comp_type_returner(element);
    let kind = arena.value_type_universe(GroundSort::Computation, Level::zero());
    let declaration = staging.codata(
        LevelSignature::monomorphic(),
        vec![universe],
        vec![head],
        kind,
    );
    let codata = environment
        .add_decl(declaration)
        .expect("a codata family over one code")
        .position();
    (data, codata)
}

/// A type whose formation owes one obligation of `kind`. The unit value is
/// not a code, so the obligation fails on it. The code of the unit type
/// makes it hold.
///
/// # Specification
/// trivial.
fn declared(
    arena: &mut TermArena,
    kind: Kind,
    owes: Owes,
    (data, codata): (ConstantIndex, ConstantIndex),
) -> ValueTypeId
{
    let unit_type = arena.value_type_unit();
    let code = arena.value_quote(unit_type);
    let input = match owes {
        Owes::Holds => code,
        Owes::Fails => arena.value_unit(),
    };
    match kind {
        Kind::Endpoints => {
            let universe = arena.value_type_universe(GroundSort::Value, Level::zero());
            arena.value_type_path(universe, code, input)
        },
        Kind::Universe => arena.value_type_element(input, Level::zero()),
        Kind::Data => arena.value_type_data(data, vec![input]),
        Kind::Codata => {
            let boxed = arena.comp_type_codata(codata, vec![input]);
            arena.value_type_thunk(boxed)
        },
    }
}

/// Stage the type of `kind` that owes as `owes` states, as an axiom or a
/// definition, and give the verdict of its admission.
///
/// # Specification
/// trivial.
fn declare(
    environment: &mut Environment,
    (kind, form, owes): (Kind, Form, Owes),
    families: (ConstantIndex, ConstantIndex),
) -> Result<(), KernelError>
{
    let mut staging = environment.stage();
    let declared = declared(staging.arena(), kind, owes, families);
    let declaration = match form {
        Form::Axiom => staging.axiom(LevelSignature::monomorphic(), declared),
        Form::Definition => {
            let body = staging.arena().value_unit();
            staging.def(LevelSignature::monomorphic(), declared, body)
        },
    };
    environment.add_decl(declaration).map(|_admitted| ())
}

/// The verdict of `declaration` alone, and of it after `before` in one
/// environment.
///
/// # Specification
/// trivial.
fn alone_and_after(
    before: (Kind, Form, Owes),
    declaration: (Kind, Form, Owes),
) -> (Result<(), KernelError>, Result<(), KernelError>)
{
    let mut alone = Environment::new();
    let held = families(&mut alone);
    let single = declare(&mut alone, declaration, held);
    let mut paired = Environment::new();
    let held = families(&mut paired);
    let _first = declare(&mut paired, before, held);
    (single, declare(&mut paired, declaration, held))
}

#[test]
fn a_refused_obligation_does_not_answer_a_later_declaration_6869()
{
    for kind in KINDS {
        for form in [Form::Axiom, Form::Definition] {
            let twin = (kind, form, Owes::Fails);
            let (alone, after) = alone_and_after(twin, twin);
            assert!(
                alone.is_err(),
                "{kind:?} {form:?}: the declaration alone is refused"
            );
            assert_eq!(
                alone, after,
                "{kind:?} {form:?}: its refused twin does not change the verdict"
            );
        }
    }
}

#[test]
fn a_held_obligation_answers_a_later_declaration_6869()
{
    for kind in KINDS {
        let twin = (kind, Form::Axiom, Owes::Holds);
        let (alone, after) = alone_and_after(twin, twin);
        assert_eq!(Ok(()), alone, "{kind:?}: the declaration alone is admitted");
        assert_eq!(
            Ok(()),
            after,
            "{kind:?}: its admitted twin does not change the verdict"
        );
        let refused = (kind, Form::Axiom, Owes::Fails);
        let (alone, after) = alone_and_after(twin, refused);
        assert!(
            alone.is_err(),
            "{kind:?}: the failing declaration alone is refused"
        );
        assert_eq!(
            alone, after,
            "{kind:?}: an admitted neighbour does not change the verdict"
        );
    }
}
