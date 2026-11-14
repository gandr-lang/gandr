use gandr_core_term::Classifier;
use gandr_core_term::CoreArena;
use gandr_core_term::Sort;
use gandr_core_term::Zone;
use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::GroundSort;
use quenchant_shape::shape::Maybe;

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

#[test]
fn a_second_unfold_of_a_code_takes_its_held_step()
{
    // def Name : Type = Integer ; and the static redex (\A. El A * El A)
    // String.
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let string = arena.value_type_base(BaseType::String);
    let body = arena.value_quote(integer);
    let string_code = arena.value_quote(string);
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let element = arena.value_type_element(bound, Level::zero());
    let product = arena.value_type_product(&[element, element]);
    let quoted = arena.value_quote(product);
    let lambda = arena.value_static_lambda(quoted);
    let redex = arena.value_static_application(lambda, string_code);
    let universe = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let constant = ConstantIndex::from(0_usize);
    let name = arena.value_constant(constant);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let declared = form_value_type(&mut context, universe).unwrap();
    assert_eq!(
        context.adopt(constant, Maybe::Present(declared), Maybe::Present(body)),
        Ok(())
    );
    let first = context.unfold(redex);
    assert!(
        matches!(first, Ok(Maybe::Present(_))),
        "a static redex unfolds: {first:?}"
    );
    let minted = context.arena().watermark();
    assert_eq!(
        (context.unfold(redex), context.arena().watermark()),
        (first, minted),
        "a second unfold gives the held reduct and mints no instance again"
    );
    let [certified, held] = [(); 2].map(|()| {
        context.start_support();
        let reduct = context.unfold(name);
        (reduct, context.finish_support())
    });
    assert!(
        matches!(certified.0, Ok(Maybe::Present(_))) && !certified.1.consulted().is_empty(),
        "a defined name unfolds and logs its definition as consulted: {certified:?}"
    );
    assert_eq!(
        held, certified,
        "a held step gives the same reduct and logs the same consult"
    );
}
