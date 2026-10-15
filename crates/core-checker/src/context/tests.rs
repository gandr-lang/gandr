use gandr_core_term::Classifier;
use gandr_core_term::CoreArena;
use gandr_core_term::Sort;
use gandr_core_term::Zone;
use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::GroundSort;

use super::Atom;
use super::CheckBudget;
use super::CheckingContext;
use crate::formation::classify_value_type;
use crate::formation::form_value_type;
use crate::refusal::CheckRefusal;
use crate::refusal::Mismatch;

/// The classifier of a value type at level zero.
///
/// # Specification
/// trivial.
fn small() -> Classifier
{
    Classifier {
        sort: GroundSort::Value,
        level: Level::zero(),
    }
}

#[test]
fn the_producer_declares_the_rigid_base_atoms()
{
    let mut arena = CoreArena::new();
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let atoms = [
        (Atom::Unit, None),
        (Atom::Integer, Some(BaseType::Integer)),
        (Atom::String, Some(BaseType::String)),
    ];
    for (atom, base) in atoms {
        let declared = context.atom(atom);
        let node = context.arena().value_type(declared.id()).cloned();
        assert_eq!(
            node,
            Some(base.map_or_else(
                gandr_core_term::ValueType::unit,
                gandr_core_term::ValueType::Base
            )),
            "the context mints {atom:?} as the rigid atom of its name"
        );
        let formed = form_value_type(&mut context, declared.id()).unwrap();
        assert_eq!(
            classify_value_type(&context, formed),
            Ok(small()),
            "every atom is a small value type"
        );
    }
}

#[test]
fn an_undeclared_type_name_is_refused_by_name()
{
    let mut arena = CoreArena::new();
    let name = arena.value_constant(ConstantIndex::from(5_usize));
    let decoded = arena.value_type_element(name, Level::zero());
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    assert_eq!(
        form_value_type(&mut context, decoded),
        Err(CheckRefusal::UnknownConstant {
            at: name,
            constant: ConstantIndex::from(5_usize),
        }),
        "a decode of a name no declaration supplied is refused naming the constant"
    );
}

#[test]
fn a_universe_typed_hypothesis_becomes_a_type_variable()
{
    let mut arena = CoreArena::new();
    let universe = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let decoded = arena.value_type_element(bound, Level::zero());
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    context.binders().open(Zone::Intuitionistic, universe);
    let formed = form_value_type(&mut context, decoded).unwrap();
    assert_eq!(
        classify_value_type(&context, formed),
        Ok(small()),
        "a hypothesis of the small universe decodes to a small type"
    );
}

#[test]
fn a_value_typed_hypothesis_does_not_become_a_type_variable()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let decoded = arena.value_type_element(bound, Level::zero());
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    context.binders().open(Zone::Intuitionistic, integer);
    let refused = form_value_type(&mut context, decoded);
    assert!(
        matches!(
            refused,
            Err(CheckRefusal::TypeMismatch(Mismatch::Value { at, synthesised, .. }))
                if at == bound && synthesised == integer
        ),
        "an integer is no code, so its decode is refused at the variable: {refused:?}"
    );
}
#[test]
fn an_adopted_untyped_body_does_not_become_a_definition()
{
    let mut arena = CoreArena::new();
    let unit = arena.value_type_unit();
    let code = arena.value_quote(unit);
    let constant = ConstantIndex::from(0_usize);
    let reference = arena.value_constant(constant);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    assert_eq!(
        context.adopt(
            constant,
            quenchant_shape::shape::Maybe::Absent(super::signature_table::Absent::Untyped),
            quenchant_shape::shape::Maybe::Present(code),
        ),
        Ok(())
    );
    assert_eq!(
        crate::synthesise_value(&mut context, reference),
        Err(CheckRefusal::UnknownConstant {
            at: reference,
            constant
        })
    );
    assert_eq!(
        context.unfold(reference),
        Ok(quenchant_shape::shape::Maybe::Absent(
            crate::unfolding::Absent::Rigid
        ))
    );
}

#[test]
fn an_adopted_abstract_type_mints_its_site_again()
{
    use crate::CheckRefusal;
    use crate::declaration::AbstractType;
    use crate::seal::ComponentOrdinal;
    use crate::seal::SealSite;
    use crate::seal::SealingSite;
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let site = SealSite::new(SealingSite::from(0_usize), ComponentOrdinal::from(0_usize));
    let declared = AbstractType::new(
        small,
        integer,
        gandr_kernel_term::SealExtent::from(1_usize),
        site,
    );
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    assert_eq!(
        context.adopt_abstract(ConstantIndex::from(0_usize), declared),
        Ok(()),
        "a reused abstract type is formed and admitted again"
    );
    assert_eq!(
        context.seal_table().sites(),
        [site],
        "adoption mints the atom's site as a judgement would"
    );
    assert_eq!(
        context.abstract_level(ConstantIndex::from(0_usize)),
        Ok(Level::zero()),
        "the adopted atom answers the level of its kind"
    );
    assert_eq!(
        context.adopt_abstract(ConstantIndex::from(1_usize), declared),
        Err(CheckRefusal::SealSiteRepeated(site)),
        "a second adoption at the same site is refused by name"
    );
    assert_eq!(
        context.abstract_types().count(),
        1,
        "the refused adoption retains no abstract type"
    );
}
