use alloc::vec::Vec;

use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::GroundSort;

use super::ArenaWatermark;
use super::CoreArena;
use super::ValueId;
use crate::classifier::Sort;
use crate::syntax::CompType;
use crate::syntax::Value;
use crate::syntax::ValueType;
use crate::syntax::Zone;

#[test]
fn flat_arena_distinguishes_type_plus_zero_and_type_minus_zero()
{
    let mut arena = CoreArena::new();
    let value_universe = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let computation_universe =
        arena.value_type_universe(Sort::Ground(GroundSort::Computation), Level::zero());
    assert_ne!(
        value_universe, computation_universe,
        "the two families at one level are two nodes"
    );
    assert_ne!(
        arena.value_type(value_universe),
        arena.value_type(computation_universe),
        "and two different nodes, not two ids over one"
    );
}

#[test]
fn flat_arena_round_trips_universe_classifier_and_level()
{
    let mut arena = CoreArena::new();
    let one = Level::zero().succ().expect("one is representable");
    let value_universe = arena.value_type_universe(Sort::Ground(GroundSort::Value), one.clone());
    let computation_universe =
        arena.value_type_universe(Sort::Ground(GroundSort::Computation), Level::zero());
    assert_eq!(
        Some(&ValueType::Universe {
            sort: Sort::Ground(GroundSort::Value),
            level: one,
        }),
        arena.value_type(value_universe),
        "the value universe reads back with its sort and level"
    );
    assert_eq!(
        Some(&ValueType::Universe {
            sort: Sort::Ground(GroundSort::Computation),
            level: Level::zero(),
        }),
        arena.value_type(computation_universe),
        "and so does the computation universe"
    );
}

#[test]
fn a_stage_refines_its_base_once()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let root = gandr_kernel_term::StageId::from(0_usize);
    let child = gandr_kernel_term::StageId::from(1_usize);
    let at_root = arena.value_type_staged(integer, gandr_kernel_term::Stage::At(root));
    assert_eq!(
        Some(&ValueType::Staged {
            base: integer,
            stage: gandr_kernel_term::Stage::At(root),
        }),
        arena.value_type(at_root),
        "a plain base is refined as it stands"
    );
    let below = gandr_kernel_term::Stage::Below {
        anchor: child,
        depth: gandr_kernel_term::StageDepth::ONE,
    };
    let restaged = arena.value_type_staged(at_root, below);
    assert_eq!(
        Some(&ValueType::Staged {
            base: integer,
            stage: below,
        }),
        arena.value_type(restaged),
        "a staged base gives up its stage rather than nesting it"
    );
}

#[test]
fn a_decoded_quote_is_the_quoted_type()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let returner = arena.comp_type_returner(integer);
    let value_code = arena.value_quote(integer);
    let computation_code = arena.value_quote_computation(returner);
    let mark = arena.watermark();
    assert_eq!(
        integer,
        arena.value_type_element(value_code, Level::zero()),
        "the value decode of a value quote is the quoted type"
    );
    assert_eq!(
        returner,
        arena.comp_type_element(computation_code, Level::zero()),
        "the computation decode of a computation quote is the quoted type"
    );
    assert_eq!(mark, arena.watermark(), "neither decode minted a node");

    let mismatched = arena.comp_type_element(value_code, Level::zero());
    assert_eq!(
        Some(&CompType::Element {
            code: value_code,
            target: Level::zero(),
        }),
        arena.comp_type(mismatched),
        "a quote of the other sort is not decoded"
    );
    let variable = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let neutral = arena.value_type_element(variable, Level::zero());
    assert_eq!(
        Some(&ValueType::Element {
            code: variable,
            target: Level::zero(),
        }),
        arena.value_type(neutral),
        "a code that is not a quote stands"
    );
}

#[test]
fn a_child_id_is_strictly_below_its_parent()
{
    let mut arena = CoreArena::new();
    let unit = arena.value_unit();
    let pair = arena.value_tuple(&[unit, unit]);
    assert!(
        unit < pair,
        "constructor-only minting orders child below parent"
    );
}

#[test]
fn truncating_to_a_watermark_drops_later_nodes()
{
    let mut arena = CoreArena::new();
    let kept = arena.value_unit();
    let mark = arena.watermark();
    let dropped = arena.value_unit();
    arena.truncate_to(mark);
    assert!(
        arena.value(kept).is_some(),
        "content below the mark survives"
    );
    assert!(
        arena.value(dropped).is_none(),
        "an id minted past the mark dangles after truncation"
    );
    arena.truncate_to(mark);
    assert!(
        arena.value(kept).is_some(),
        "truncating twice to the same mark is a no-op"
    );
}

#[test]
fn allocation_suffixes_keep_their_family()
{
    let mut arena = CoreArena::new();
    let unit_type = arena.value_type_unit();
    let unit = arena.value_unit();
    let returned = arena.computation_return(unit);
    let returner = arena.comp_type_returner(unit_type);
    let before = arena.watermark();
    let product = arena.value_type_product(&[unit_type, unit_type]);
    let pair = arena.value_tuple(&[unit, unit]);
    let bound = arena.computation_bind(returned, returned);
    let thunked = arena.value_type_thunk(returner);
    let lifted = arena.comp_type_returner(thunked);
    let after = arena.watermark();
    assert_eq!(arena.values_since(before).collect::<Vec<_>>(), [pair]);
    assert_eq!(arena.computations_since(before).collect::<Vec<_>>(), [
        bound
    ]);
    assert_eq!(
        arena.value_types_since(before).collect::<Vec<_>>(),
        [product, thunked],
        "the suffix keeps allocation order"
    );
    assert_eq!(arena.comp_types_since(before).collect::<Vec<_>>(), [lifted]);
    assert_eq!(
        arena.values_since(after).len(),
        0,
        "nothing follows the latest mark"
    );
    arena.truncate_to(before);
    assert_eq!(
        arena.values_since(after).len(),
        0,
        "a stale mark answers nothing"
    );
    assert_eq!(arena.comp_types_since(after).len(), 0);
    let replacement = arena.value_unit();
    assert_eq!(
        arena.values_since(before).collect::<Vec<_>>(),
        [replacement],
        "a truncated suffix is not resurrected"
    );
    assert_eq!(arena.computations_since(before).len(), 0);
}

#[test]
fn a_dangling_id_resolves_to_nothing()
{
    let arena = CoreArena::new();
    assert!(
        arena.value(ValueId(7)).is_none(),
        "an unresolvable id yields no node rather than panicking"
    );
}

#[test]
fn the_default_watermark_is_the_empty_arena()
{
    let arena = CoreArena::new();
    assert_eq!(
        ArenaWatermark::default(),
        arena.watermark(),
        "an empty arena sits at the floor"
    );
}

#[test]
fn a_variable_records_the_zone_it_counts_in()
{
    let mut arena = CoreArena::new();
    let index = DeBruijnIndex::from(0_u32);
    let structural = arena.value_variable(Zone::Intuitionistic, index);
    let linear = arena.value_variable(Zone::Linear, index);
    assert_eq!(
        Some(&Value::Variable {
            zone: Zone::Intuitionistic,
            index,
        }),
        arena.value(structural),
        "the intuitionistic occurrence keeps its zone"
    );
    assert_ne!(
        arena.value(structural),
        arena.value(linear),
        "one index in two zones is two different occurrences"
    );
}

#[test]
fn flat_arena_round_trips_all_static_argument_shapes()
{
    let mut arena = CoreArena::new();
    let family = arena.value_constant(ConstantIndex::from(0_usize));
    let integer = arena.value_type_base(BaseType::Integer);
    let returner = arena.comp_type_returner(integer);
    let quote = arena.value_quote(integer);
    let computation_quote = arena.value_quote_computation(returner);
    let variable = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let constant = arena.value_constant(ConstantIndex::from(1_usize));
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let lambda = arena.value_static_lambda(bound);
    let nested = arena.value_static_application(constant, quote);
    for argument in [quote, computation_quote, variable, constant, lambda, nested] {
        let applied = arena.value_static_application(family, argument);
        assert_eq!(
            Some(&Value::StaticApplication(family, argument)),
            arena.value(applied),
            "the family applied to {:?} reads back with its head and argument",
            arena.value(argument)
        );
    }
    assert_eq!(
        Some(&Value::StaticLambda(bound)),
        arena.value(lambda),
        "the static lambda reads back over its body"
    );

    let redex = arena.value_static_application(lambda, quote);
    assert_eq!(
        Some(&Value::StaticApplication(lambda, quote)),
        arena.value(redex),
        "a lambda head is left unreduced: the redex is representable"
    );

    let universe = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let pi = arena.value_type_static_pi(universe, universe);
    assert_eq!(
        Some(&ValueType::StaticPi {
            domain: universe,
            codomain: universe,
        }),
        arena.value_type(pi),
        "the static Pi reads back with its domain and codomain"
    );
}
#[test]
fn index_boundaries_preserve_identity_or_saturate()
{
    for raw in [0_u32, 1, u32::MAX] {
        let offset = super::id_offset(super::ArenaIndex(raw));
        assert_eq!(usize::try_from(raw).unwrap_or(usize::MAX), offset.0);
        assert_eq!(raw, super::id_index(offset).0);
    }
    if let Some(above) = usize::try_from(u32::MAX)
        .ok()
        .and_then(|limit| limit.checked_add(1))
    {
        assert_eq!(u32::MAX, super::id_index(super::ArenaLength(above)).0);
    }
}

#[test]
fn all_families_truncate_without_resurrecting_nodes()
{
    let mut arena = CoreArena::new();
    let kept_value = arena.value_unit();
    let kept_type = arena.value_type_unit();
    let kept_comp = arena.computation_return(kept_value);
    let kept_comp_type = arena.comp_type_returner(kept_type);
    let mark = arena.watermark();
    let dropped_value = arena.value_constant(ConstantIndex::from(17_usize));
    let dropped_type = arena.value_type_base(BaseType::Integer);
    let dropped_comp = arena.computation_force(dropped_value);
    let dropped_comp_type = arena.comp_type_arrow(dropped_type, kept_comp_type);
    let later = arena.watermark();
    assert_eq!(
        Some(&Value::Constant(ConstantIndex::from(17_usize))),
        arena.value(dropped_value)
    );
    assert_eq!(
        Some(&ValueType::Base(BaseType::Integer)),
        arena.value_type(dropped_type)
    );
    assert_eq!(
        Some(&crate::Computation::Force(dropped_value)),
        arena.computation(dropped_comp)
    );
    assert_eq!(
        Some(&CompType::Arrow {
            domain: dropped_type,
            codomain: kept_comp_type
        }),
        arena.comp_type(dropped_comp_type)
    );
    arena.truncate_to(mark);
    assert_eq!(Some(&Value::unit()), arena.value(kept_value));
    assert_eq!(Some(&ValueType::unit()), arena.value_type(kept_type));
    assert_eq!(
        Some(&crate::Computation::Return(kept_value)),
        arena.computation(kept_comp)
    );
    assert_eq!(
        Some(&CompType::Returner {
            result: kept_type,
            effects: crate::effect::EffectRow::EMPTY
        }),
        arena.comp_type(kept_comp_type)
    );
    assert_eq!(None, arena.value(dropped_value));
    assert_eq!(None, arena.value_type(dropped_type));
    assert_eq!(None, arena.computation(dropped_comp));
    assert_eq!(None, arena.comp_type(dropped_comp_type));
    arena.truncate_to(later);
    assert_eq!(mark, arena.watermark());
    let replacement = arena.value_tuple(&[kept_value, kept_value]);
    assert_eq!(dropped_value, replacement);
    assert_eq!(
        Some(&Value::Tuple([kept_value, kept_value].into())),
        arena.value(replacement)
    );
    arena.truncate_to(ArenaWatermark::default());
    arena.truncate_to(later);
    assert_eq!(ArenaWatermark::default(), arena.watermark());
    assert_eq!(None, arena.value(kept_value));
    assert_eq!(None, arena.value_type(kept_type));
    assert_eq!(None, arena.computation(kept_comp));
    assert_eq!(None, arena.comp_type(kept_comp_type));
}

#[test]
fn distinct_children_survive_every_compound_former()
{
    let mut arena = CoreArena::new();
    let first = arena.value_unit();
    let second = arena.value_constant(ConstantIndex::from(17_usize));
    let left = arena.computation_return(first);
    let right = arena.computation_return(second);
    let domain = arena.value_type_unit();
    let other = arena.value_type_base(BaseType::Integer);
    let result = arena.comp_type_returner(other);
    let level = Level::zero().succ().expect("one");
    let values = [
        (
            arena.value_tuple(&[first, second]),
            Value::Tuple([first, second].into()),
        ),
        (
            arena.value_injection(gandr_kernel_term::Side::Left.into(), first),
            Value::Injection(gandr_kernel_term::Side::Left.into(), first),
        ),
        (
            arena.value_injection(gandr_kernel_term::Side::Right.into(), second),
            Value::Injection(gandr_kernel_term::Side::Right.into(), second),
        ),
        (arena.value_thunk(right), Value::Thunk(right)),
        (arena.value_lift(level.clone(), second), Value::Lift {
            target: level.clone(),
            body: second,
        }),
        (arena.value_quote(other), Value::Quote(other)),
        (
            arena.value_quote_computation(result),
            Value::QuoteComputation(result),
        ),
    ];
    for (id, node) in values {
        assert!(id > second);
        assert_eq!(Some(&node), arena.value(id));
    }
    let computations = [
        (
            arena.computation_lambda(right),
            crate::Computation::Lambda(right),
        ),
        (
            arena.computation_fixpoint(left, gandr_kernel_term::FixpointEvidence::Partial),
            crate::Computation::Fixpoint {
                body: left,
                evidence: gandr_kernel_term::FixpointEvidence::Partial,
            },
        ),
        (
            arena.computation_fixpoint(
                right,
                gandr_kernel_term::FixpointEvidence::StructuralDescent,
            ),
            crate::Computation::Fixpoint {
                body: right,
                evidence: gandr_kernel_term::FixpointEvidence::StructuralDescent,
            },
        ),
        (
            arena.computation_application(left, second),
            crate::Computation::Application(left, second),
        ),
        (
            arena.computation_return(second),
            crate::Computation::Return(second),
        ),
        (
            arena.computation_bind(left, right),
            crate::Computation::Bind(left, right),
        ),
        (
            arena.computation_ascribe(right, result),
            crate::Computation::Ascribe {
                body: right,
                ty: result,
            },
        ),
        (
            arena.computation_force(second),
            crate::Computation::Force(second),
        ),
        (
            arena.computation_case(first, &[left, right]),
            crate::Computation::Case {
                scrutinee: first,
                branches: [left, right].into(),
            },
        ),
        (
            arena.computation_split(second, crate::ComponentCount::from(2_usize), left),
            crate::Computation::Split {
                scrutinee: second,
                arity: crate::ComponentCount::from(2_usize),
                motive: crate::SplitMotive::Ambient,
                body: left,
            },
        ),
        (
            arena.computation_dependent_split(
                second,
                crate::ComponentCount::from(2_usize),
                result,
                left,
            ),
            crate::Computation::Split {
                scrutinee: second,
                arity: crate::ComponentCount::from(2_usize),
                motive: crate::SplitMotive::Scrutinee(result),
                body: left,
            },
        ),
    ];
    for (id, node) in computations {
        assert!(id > right);
        assert_eq!(Some(&node), arena.computation(id));
    }
    let types = [
        (
            arena.value_type_product(&[domain, other]),
            ValueType::Product([domain, other].into()),
        ),
        (
            arena.value_type_product(&[other, domain, other]),
            ValueType::Product([other, domain, other].into()),
        ),
        (arena.value_type_sigma(domain, other), ValueType::Sigma {
            first: domain,
            second: other,
        }),
        (arena.value_type_unit(), ValueType::unit()),
        (
            arena.value_type_sum(&[domain, other]),
            ValueType::Sum([domain, other].into()),
        ),
        (
            arena.value_type_sum(&[other, other, domain]),
            ValueType::Sum([other, other, domain].into()),
        ),
        (
            arena.value_type_sum(&[]),
            ValueType::Sum(alloc::boxed::Box::default()),
        ),
        (arena.value_type_thunk(result), ValueType::Thunk(result)),
        (
            arena.value_type_lift(other, level.clone()),
            ValueType::Lift {
                inner: other,
                target: level,
            },
        ),
        (
            arena.value_type_abstract(ConstantIndex::from(23_usize)),
            ValueType::Abstract(ConstantIndex::from(23_usize)),
        ),
    ];
    for (id, node) in types {
        assert!(id > other);
        assert_eq!(Some(&node), arena.value_type(id));
    }
    let comp_types = [
        (arena.comp_type_returner(domain), CompType::Returner {
            result: domain,
            effects: crate::effect::EffectRow::EMPTY,
        }),
        (arena.comp_type_arrow(domain, result), CompType::Arrow {
            domain,
            codomain: result,
        }),
        (arena.comp_type_pi(other, result), CompType::Pi {
            domain: other,
            codomain: result,
        }),
    ];
    for (id, node) in comp_types {
        assert!(id > result);
        assert_eq!(Some(&node), arena.comp_type(id));
    }
}

#[test]
fn a_mark_keeps_its_index_and_its_body()
{
    let mut arena = CoreArena::new();
    let first = arena.value_hole(crate::hole::HoleId::from(4_u32));
    let second = arena.value_unit();
    let marked_first = arena.value_mark(crate::hole::MarkIndex::from(0_u32), first);
    let marked_second = arena.value_mark(crate::hole::MarkIndex::from(1_u32), second);
    assert!(marked_first > first && marked_second > second);
    assert_eq!(
        arena.value(marked_first),
        Some(&Value::Mark {
            mark: crate::hole::MarkIndex::from(0_u32),
            body: first,
        })
    );
    assert_eq!(
        arena.value(marked_second),
        Some(&Value::Mark {
            mark: crate::hole::MarkIndex::from(1_u32),
            body: second,
        })
    );
    let left = arena.computation_hole(crate::hole::HoleId::from(4_u32));
    let right = arena.computation_return(second);
    let marked_left = arena.computation_mark(crate::hole::MarkIndex::from(2_u32), left);
    let marked_right = arena.computation_mark(crate::hole::MarkIndex::from(3_u32), right);
    assert!(marked_left > left && marked_right > right);
    assert_eq!(
        arena.computation(marked_left),
        Some(&crate::Computation::Mark {
            mark: crate::hole::MarkIndex::from(2_u32),
            body: left,
        })
    );
    assert_eq!(
        arena.computation(marked_right),
        Some(&crate::Computation::Mark {
            mark: crate::hole::MarkIndex::from(3_u32),
            body: right,
        })
    );
}
