//! The replay of a match's cover derivation at its definition's admission.

use anodized::spec;
use gandr_kernel_core::Environment;
use gandr_kernel_core::KernelError;
use gandr_kernel_strata::Level;
use gandr_kernel_term::CellIndex;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldCount;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::LevelSignature;
use gandr_kernel_term::cover::Cases;
use gandr_kernel_term::cover::Cover;
use gandr_kernel_term::cover::CoverRefusal;
use gandr_kernel_term::cover::Covered;
use gandr_kernel_term::cover::Loop;
use gandr_kernel_term::cover::Step;
use gandr_kernel_term::cover::StepId;

/// Admit `Two`, with `Z` of no field and `S` of one unit field, and answer its
/// position.
///
/// # Specification
/// trivial.
#[spec(captures: position = environment.entries().len(), ensures: |ret| usize::from(ret) == position)]
fn two(environment: &mut Environment) -> ConstantIndex
{
    let mut staging = environment.stage();
    let arena = staging.arena();
    let unit = arena.value_type_unit();
    let kind = arena.value_type_universe(GroundSort::Value, Level::zero());
    let declaration = staging.data(
        LevelSignature::monomorphic(),
        vec![],
        vec![vec![], vec![unit]],
        kind,
    );
    environment
        .add_decl(declaration)
        .expect("well-formed native data")
        .position()
}

/// How a derivation for `case_of_two` is broken.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Broken
{
    /// Not broken: the derivation the lowering records.
    Whole,
    /// The split lists `S` before `Z`.
    Order,
    /// The split leaves `S` out, and its branch with it.
    Dropped,
    /// The split gives `S` two fields.
    Fields,
    /// The split names a family the environment does not hold.
    Family,
    /// The split lists a loop `Two` does not owe.
    Loop,
    /// The split names a step minted after it.
    Dangling,
    /// The split is absurd, over a case with branches.
    Absurd,
    /// The root names another node of the tree.
    Root,
}

/// The derivation of `case Two { Z => …, S(_) => … }`, broken as `broken`.
///
/// # Specification
/// trivial.
fn derivation(
    family: ConstantIndex,
    broken: Broken,
) -> Cover
{
    let mut cover = Cover::new();
    let zero = cover.mint(Step::Var(0));
    let succ = cover.mint(Step::Var(1));
    let constructors = match broken {
        Broken::Order => vec![
            (ConstructorTag::from(1_usize), FieldCount::from(1_usize)),
            (ConstructorTag::from(0_usize), FieldCount::from(0_usize)),
        ],
        Broken::Dropped => vec![(ConstructorTag::from(0_usize), FieldCount::from(0_usize))],
        Broken::Fields => vec![
            (ConstructorTag::from(0_usize), FieldCount::from(0_usize)),
            (ConstructorTag::from(1_usize), FieldCount::from(2_usize)),
        ],
        Broken::Whole
        | Broken::Family
        | Broken::Loop
        | Broken::Dangling
        | Broken::Absurd
        | Broken::Root => vec![
            (ConstructorTag::from(0_usize), FieldCount::from(0_usize)),
            (ConstructorTag::from(1_usize), FieldCount::from(1_usize)),
        ],
    };
    let loops = match broken {
        Broken::Loop => vec![Loop::new(family, CellIndex::from(0_usize))],
        Broken::Whole
        | Broken::Order
        | Broken::Dropped
        | Broken::Fields
        | Broken::Family
        | Broken::Dangling
        | Broken::Absurd
        | Broken::Root => vec![],
    };
    let branches = match broken {
        Broken::Dropped => vec![zero],
        Broken::Loop => vec![zero, succ, zero],
        Broken::Dangling => vec![zero, StepId::from(9_u32)],
        Broken::Whole
        | Broken::Order
        | Broken::Fields
        | Broken::Family
        | Broken::Absurd
        | Broken::Root => vec![zero, succ],
    };
    let cases = match broken {
        Broken::Family => Cases::Data {
            family: ConstantIndex::from(usize::from(family).saturating_add(7)),
            constructors,
            loops,
        },
        Broken::Absurd => Cases::Absurd,
        Broken::Whole
        | Broken::Order
        | Broken::Dropped
        | Broken::Fields
        | Broken::Loop
        | Broken::Dangling
        | Broken::Root => Cases::Data {
            family,
            constructors,
            loops,
        },
    };
    let branches = if broken == Broken::Absurd {
        vec![]
    }
    else {
        branches
    };
    let _root = cover.mint(Step::Split { cases, branches });
    cover
}

/// Offer `def f(t : Two) -> unit = case t { Z => (), S(_) => () }` with the
/// derivation broken as `broken`.
///
/// # Specification
/// trivial.
fn case_of_two(
    environment: &mut Environment,
    family: ConstantIndex,
    broken: Broken,
) -> Result<(), KernelError>
{
    let mut staging = environment.stage();
    let arena = staging.arena();
    let datatype = arena.value_type_data(family, vec![]);
    let unit_type = arena.value_type_unit();
    let unit = arena.value_unit();
    let returned = arena.computation_return(unit);
    let scrutinee = arena.value_variable(DeBruijnIndex::from(0_u32));
    let motive = arena.comp_type_returner(unit_type);
    let succ = arena.computation_lambda(returned);
    let case = arena.computation_data_case(scrutinee, motive, vec![returned, succ]);
    let function = arena.computation_lambda(case);
    let body = arena.value_thunk(function);
    let arrow = arena.comp_type_arrow(datatype, motive);
    let declared = arena.value_type_thunk(arrow);
    let root = if broken == Broken::Root { succ } else { case };
    let declaration = staging
        .def(LevelSignature::monomorphic(), declared, body)
        .covered(vec![Covered {
            root,
            cover: derivation(family, broken),
        }]);
    environment.add_decl(declaration).map(|_admitted| ())
}

#[test]
fn a_derivation_that_follows_its_tree_is_admitted_5104()
{
    let mut environment = Environment::new();
    let family = two(&mut environment);
    assert_eq!(case_of_two(&mut environment, family, Broken::Whole), Ok(()));
}

#[test]
fn every_broken_derivation_is_refused_by_its_rule_5104()
{
    let mut environment = Environment::new();
    let family = two(&mut environment);
    let split = StepId::from(2_u32);
    for (broken, refusal) in [
        (Broken::Order, CoverRefusal::ConstructorOrder(split)),
        (Broken::Dropped, CoverRefusal::ConstructorCount(split)),
        (Broken::Fields, CoverRefusal::FieldCount(split)),
        (Broken::Family, CoverRefusal::UnknownFamily(split)),
        (Broken::Loop, CoverRefusal::Loops(split)),
        (Broken::Dangling, CoverRefusal::Dangling(split)),
        (Broken::Absurd, CoverRefusal::Tree(split)),
        (Broken::Root, CoverRefusal::Tree(split)),
    ] {
        assert_eq!(
            case_of_two(&mut environment, family, broken),
            Err(KernelError::CoverDisagrees(refusal)),
            "{broken:?}"
        );
    }
}
