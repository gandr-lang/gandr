use alloc::sync::Arc;
use alloc::vec;
use alloc::vec::Vec;

use gandr_core_term::CoreArena;
use gandr_core_term::DataSignature;
use gandr_core_term::Sort;
use gandr_core_term::hole::HoleId;
use gandr_core_term::pattern::Pattern;
use gandr_core_term::pattern::PatternId;
use gandr_core_term::pattern::Patterns;
use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::Side;

use super::CoverageFault;
use super::Exhaustiveness;
use super::Redundancy;
use super::cover;
use crate::context::CheckBudget;
use crate::context::CheckingContext;
use crate::fixture::integer_literal;
use crate::formation::form_value_type;
use crate::refusal::CheckRefusal;

/// Answer `arms` over `scrutinee` as the pair the tests compare.
///
/// # Specification
/// trivial.
fn answer(
    context: &mut CheckingContext<'_>,
    scrutinee: gandr_core_term::ValueTypeId,
    patterns: &Patterns,
    arms: &[PatternId],
) -> (Exhaustiveness, Vec<Redundancy>)
{
    let scrutinee = form_value_type(context, scrutinee).unwrap();
    let coverage = cover(context, scrutinee, patterns, arms).unwrap();
    (coverage.exhaustiveness(), coverage.arms().to_vec())
}

#[test]
fn usefulness_decides_exhaustiveness_and_redundancy()
{
    let mut arena = CoreArena::new();
    let unit = arena.value_type_unit();
    let sum = arena.value_type_sum(&[unit, unit]);
    let mut patterns = Patterns::new();
    let wildcard = patterns.mint(Pattern::Wildcard);
    let left = patterns.mint(Pattern::Injection(Side::Left, wildcard));
    let right = patterns.mint(Pattern::Injection(Side::Right, wildcard));
    let binder = patterns.mint(Pattern::Binder);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);

    assert_eq!(
        answer(&mut context, sum, &patterns, &[left, right, binder]),
        (Exhaustiveness::Exhaustive, vec![
            Redundancy::Irredundant,
            Redundancy::Irredundant,
            Redundancy::Redundant
        ]),
        "both injections cover the sum, so the binder below them is redundant"
    );
    assert_eq!(
        answer(&mut context, sum, &patterns, &[left]),
        (Exhaustiveness::Inexhaustive, vec![Redundancy::Irredundant]),
        "the right injection is missing"
    );
    assert_eq!(
        answer(&mut context, sum, &patterns, &[]),
        (Exhaustiveness::Inexhaustive, Vec::new()),
        "no arm covers an inhabited type"
    );
    assert_eq!(
        answer(&mut context, sum, &patterns, &[binder, left]),
        (Exhaustiveness::Exhaustive, vec![
            Redundancy::Irredundant,
            Redundancy::Redundant
        ]),
        "a binder covers everything below it"
    );

    let mut short = CoreArena::new();
    let unit = short.value_type_unit();
    let sum = short.value_type_sum(&[unit, unit]);
    let mut context = CheckingContext::new(&mut short, CheckBudget::from(1_usize));
    let sum = crate::formation::FormedValueType::derived(sum);
    assert_eq!(
        cover(&mut context, sum, &patterns, &[left, right]),
        Err(CoverageFault::Refused(CheckRefusal::BudgetExceeded {
            budget: CheckBudget::from(1_usize),
        })),
        "each problem costs a step of the allowance"
    );
    let mut larger = Patterns::new();
    let mut foreign = larger.mint(Pattern::Wildcard);
    for _ in 0_u8 .. 8 {
        foreign = larger.mint(Pattern::Wildcard);
    }
    assert_eq!(
        cover(&mut context, sum, &patterns, &[foreign]),
        Err(CoverageFault::DanglingPattern(foreign)),
        "a pattern outside the table is refused"
    );
}

#[test]
fn literals_never_complete_and_nested_columns_specialise()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let unit = arena.value_type_unit();
    let sum = arena.value_type_sum(&[unit, unit]);
    let product = arena.value_type_product(&[integer, sum]);
    let mut patterns = Patterns::new();
    let wildcard = patterns.mint(Pattern::Wildcard);
    let zero = patterns.mint(Pattern::Literal(integer_literal()));
    let unit_pattern = patterns.mint(Pattern::Unit);
    let left = patterns.mint(Pattern::Injection(Side::Left, unit_pattern));
    let right = patterns.mint(Pattern::Injection(Side::Right, wildcard));
    let zero_left = patterns.mint(Pattern::Pair(zero, left));
    let any_right = patterns.mint(Pattern::Pair(wildcard, right));
    let any_left = patterns.mint(Pattern::Pair(wildcard, left));
    let any = patterns.mint(Pattern::Pair(wildcard, wildcard));
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);

    assert_eq!(
        answer(&mut context, product, &patterns, &[zero_left, any_right]),
        (Exhaustiveness::Inexhaustive, vec![
            Redundancy::Irredundant,
            Redundancy::Irredundant
        ]),
        "one literal never covers the integers: (1, left ()) is missed"
    );
    assert_eq!(
        answer(&mut context, product, &patterns, &[
            zero_left, any_right, any_left
        ]),
        (Exhaustiveness::Exhaustive, vec![
            Redundancy::Irredundant,
            Redundancy::Irredundant,
            Redundancy::Irredundant
        ]),
        "the second column completes the sum below a wildcard first column"
    );
    assert_eq!(
        answer(&mut context, product, &patterns, &[any, zero_left]),
        (Exhaustiveness::Exhaustive, vec![
            Redundancy::Irredundant,
            Redundancy::Redundant
        ]),
        "a nested pair of wildcards covers the product"
    );
    let integer = form_value_type(&mut context, integer).unwrap();
    assert_eq!(
        cover(&mut context, integer, &patterns, &[left]),
        Err(CoverageFault::IllTypedPattern {
            pattern: left,
            column: integer.id(),
        }),
        "an injection cannot stand at a base type"
    );
}

#[test]
fn a_nominal_type_is_complete_when_every_constructor_stands()
{
    let mut arena = CoreArena::new();
    let unit = arena.value_type_unit();
    let kind = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let datatype = arena.value_type_data(ConstantIndex::from(0_usize), Vec::new());
    let empty = arena.value_type_data(ConstantIndex::from(1_usize), Vec::new());
    let mut patterns = Patterns::new();
    let wildcard = patterns.mint(Pattern::Wildcard);
    let unit_pattern = patterns.mint(Pattern::Unit);
    let none = patterns.mint(Pattern::Constructor {
        tag: ConstructorTag::from(0_usize),
        fields: Vec::new(),
    });
    let some_unit = patterns.mint(Pattern::Constructor {
        tag: ConstructorTag::from(1_usize),
        fields: vec![unit_pattern],
    });
    let some = patterns.mint(Pattern::Constructor {
        tag: ConstructorTag::from(1_usize),
        fields: vec![wildcard],
    });
    let pair = patterns.mint(Pattern::Pair(wildcard, wildcard));
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    context.record_data(
        ConstantIndex::from(0_usize),
        Arc::new(DataSignature::new(
            Vec::new(),
            vec![Vec::new(), vec![unit]],
            kind,
        )),
    );
    context.record_data(
        ConstantIndex::from(1_usize),
        Arc::new(DataSignature::new(Vec::new(), Vec::new(), kind)),
    );

    assert_eq!(
        answer(&mut context, datatype, &patterns, &[none, some]),
        (Exhaustiveness::Exhaustive, vec![
            Redundancy::Irredundant,
            Redundancy::Irredundant
        ]),
        "both constructors stand"
    );
    assert_eq!(
        answer(&mut context, datatype, &patterns, &[some_unit]),
        (Exhaustiveness::Inexhaustive, vec![Redundancy::Irredundant]),
        "the first constructor is missing"
    );
    assert_eq!(
        answer(&mut context, datatype, &patterns, &[none, some_unit, some]),
        (Exhaustiveness::Exhaustive, vec![
            Redundancy::Irredundant,
            Redundancy::Irredundant,
            Redundancy::Redundant
        ]),
        "the unit field is covered by its only value"
    );
    assert_eq!(
        answer(&mut context, empty, &patterns, &[]),
        (Exhaustiveness::Exhaustive, Vec::new()),
        "a type without constructors is covered by no arm"
    );
    let datatype = form_value_type(&mut context, datatype).unwrap();
    assert_eq!(
        cover(&mut context, datatype, &patterns, &[pair]),
        Err(CoverageFault::IllTypedPattern {
            pattern: pair,
            column: datatype.id(),
        }),
        "a pair cannot stand at a nominal type"
    );
}

#[test]
fn a_pattern_hole_is_answered_possibly()
{
    let mut arena = CoreArena::new();
    let unit = arena.value_type_unit();
    let integer = arena.value_type_base(BaseType::Integer);
    let sum = arena.value_type_sum(&[unit, unit]);
    let mixed = arena.value_type_sum(&[integer, unit]);
    let mut patterns = Patterns::new();
    let wildcard = patterns.mint(Pattern::Wildcard);
    let left = patterns.mint(Pattern::Injection(Side::Left, wildcard));
    let right = patterns.mint(Pattern::Injection(Side::Right, wildcard));
    let hole = patterns.mint(Pattern::Hole(HoleId::from(0_u32)));
    let left_hole = patterns.mint(Pattern::Injection(Side::Left, hole));
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);

    assert_eq!(
        answer(&mut context, sum, &patterns, &[left, hole]),
        (Exhaustiveness::Possibly, vec![
            Redundancy::Irredundant,
            Redundancy::Possibly
        ]),
        "the hole may be a right injection or another left one"
    );
    assert_eq!(
        answer(&mut context, sum, &patterns, &[left, right, hole]),
        (Exhaustiveness::Exhaustive, vec![
            Redundancy::Irredundant,
            Redundancy::Irredundant,
            Redundancy::Redundant
        ]),
        "below a covering prefix the hole is redundant whatever its fill"
    );
    assert_eq!(
        answer(&mut context, sum, &patterns, &[hole, left]),
        (Exhaustiveness::Possibly, vec![
            Redundancy::Possibly,
            Redundancy::Possibly
        ]),
        "a hole above an arm may or may not cover it"
    );
    assert_eq!(
        answer(&mut context, mixed, &patterns, &[left_hole, right]),
        (Exhaustiveness::Possibly, vec![
            Redundancy::Possibly,
            Redundancy::Irredundant
        ]),
        "a hole beneath an injection may be one literal or a wildcard"
    );
}

#[test]
fn an_unknown_scrutinee_reads_the_least_and_the_widest_signature()
{
    let mut arena = CoreArena::new();
    let unknown = arena.value_type_unknown();
    let mut patterns = Patterns::new();
    let wildcard = patterns.mint(Pattern::Wildcard);
    let unit_pattern = patterns.mint(Pattern::Unit);
    let left = patterns.mint(Pattern::Injection(Side::Left, wildcard));
    let first = patterns.mint(Pattern::Constructor {
        tag: ConstructorTag::from(0_usize),
        fields: Vec::new(),
    });
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);

    assert_eq!(
        answer(&mut context, unknown, &patterns, &[wildcard]),
        (Exhaustiveness::Exhaustive, vec![Redundancy::Irredundant]),
        "a wildcard covers any type"
    );
    assert_eq!(
        answer(&mut context, unknown, &patterns, &[unit_pattern]),
        (Exhaustiveness::Exhaustive, vec![Redundancy::Irredundant]),
        "a unit pattern fixes the type as unit"
    );
    assert_eq!(
        answer(&mut context, unknown, &patterns, &[left]),
        (Exhaustiveness::Inexhaustive, vec![Redundancy::Irredundant]),
        "an injection fixes a sum, whose right side is missing"
    );
    assert_eq!(
        answer(&mut context, unknown, &patterns, &[first]),
        (Exhaustiveness::Possibly, vec![Redundancy::Irredundant]),
        "a nominal type of one constructor or of more"
    );
    assert_eq!(
        answer(&mut context, unknown, &patterns, &[]),
        (Exhaustiveness::Inexhaustive, Vec::new()),
        "the unknown type is read as inhabited"
    );
    let formed = form_value_type(&mut context, unknown).unwrap();
    assert_eq!(
        cover(&mut context, formed, &patterns, &[unit_pattern, left]),
        Err(CoverageFault::IllTypedPattern {
            pattern: left,
            column: unknown,
        }),
        "a unit and an injection cannot share a column"
    );
}
