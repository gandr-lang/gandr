use alloc::sync::Arc;
use alloc::vec;
use alloc::vec::Vec;

use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::GroundSort;

use super::ArenaWatermark;
use super::BinderPrecedence;
use super::CoreArena;
use super::ValueId;
use crate::classifier::Sort;
use crate::control::StackFrame;
use crate::effect::capability::Region;
use crate::effect::capability::RegionBinder;
use crate::memory::AccessMode;
use crate::memory::MemoryForm;
use crate::session::SessionAction;
use crate::support::Thinning;
use crate::support::ThinningRef;
use crate::syntax::CompType;
use crate::syntax::ComponentCount;
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

/// A type minted before the arena's first kept type at a region binder names
/// none without a walk; that kept type and every type minted after it are read,
/// until a truncation drops it.
#[test]
fn a_type_minted_before_the_first_region_binder_names_none()
{
    let mut arena = CoreArena::new();
    let unit = arena.value_type_unit();
    let returner = arena.comp_type_returner(unit);
    let held = arena.value_type_kept(unit, Region::Held);
    assert_eq!(
        arena.value_type_binder_precedence(held),
        BinderPrecedence::Before,
        "a type kept in the held region names no binder"
    );
    let mark = arena.watermark();
    let bound = arena.value_type_kept(unit, Region::Bound(RegionBinder::from(0_u32)));
    let later = arena.value_type_thunk(returner);
    let later_returner = arena.comp_type_returner(unit);
    assert_eq!(
        (
            arena.value_type_binder_precedence(unit),
            arena.comp_type_binder_precedence(returner)
        ),
        (BinderPrecedence::Before, BinderPrecedence::Before),
        "a type minted before the first binder names none"
    );
    assert_eq!(
        arena.value_type_binder_precedence(bound),
        BinderPrecedence::Unread,
        "the type naming the binder is read"
    );
    assert_eq!(
        (
            arena.value_type_binder_precedence(later),
            arena.comp_type_binder_precedence(later_returner)
        ),
        (BinderPrecedence::Unread, BinderPrecedence::Unread),
        "a type minted after it is read, whatever it reaches"
    );
    arena.truncate_to(mark);
    assert_eq!(
        arena.value_type_binder_precedence(bound),
        BinderPrecedence::Unread,
        "a dangling id says nothing"
    );
    let reused = arena.value_type_thunk(returner);
    assert_eq!(reused, bound, "the truncated index is minted again");
    assert_eq!(
        arena.value_type_binder_precedence(reused),
        BinderPrecedence::Before,
        "a truncation below the binder's type forgets it"
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

/// An arena frozen part way answers every read, mint, truncation and
/// comparison as one built alike and never frozen does; a clone of it shares
/// the frozen rows and owns only those minted after, and a truncation into
/// the frozen rows leaves a clone taken before untouched.
#[test]
fn a_frozen_arena_answers_as_it_did_and_clones_its_own_rows_alone()
{
    // Each round mints its own content, so a read off by one across the
    // frozen boundary finds another node.
    let round = |arena: &mut CoreArena, constant: usize, ty: Option<BaseType>| {
        let value = arena.value_constant(ConstantIndex::from(constant));
        let value_type = match ty {
            Some(ty) => arena.value_type_base(ty),
            None => arena.value_type_unit(),
        };
        let computation = arena.computation_return(value);
        let comp_type = arena.comp_type_returner(value_type);
        (value, value_type, computation, comp_type)
    };
    let shares = |left: &CoreArena, right: &CoreArena| {
        left.values
            .frozen
            .as_ref()
            .zip(right.values.frozen.as_ref())
            .is_some_and(|(left, right)| Arc::ptr_eq(left, right))
    };
    let mut plain = CoreArena::new();
    let mut frozen = CoreArena::new();
    let first = round(&mut plain, 0, Some(BaseType::Integer));
    assert_eq!(first, round(&mut frozen, 0, Some(BaseType::Integer)));
    let mark = frozen.watermark();
    frozen.freeze();
    assert_eq!(mark, frozen.watermark(), "a freeze keeps the watermark");
    assert_eq!(plain, frozen, "and every node");
    assert!(frozen.values.own.is_empty(), "every row is frozen");

    let mut copy = frozen.clone();
    assert!(shares(&copy, &frozen), "a clone shares the frozen rows");
    let second = round(&mut plain, 1, None);
    assert_eq!(
        second,
        round(&mut copy, 1, None),
        "ids continue past the frozen rows"
    );
    assert_eq!(
        copy.values.own.len(),
        1,
        "the clone owns only what it minted"
    );
    assert_eq!(plain, copy);
    assert_eq!(
        copy.value(first.0),
        Some(&Value::Constant(ConstantIndex::from(0_usize)))
    );
    assert_eq!(
        copy.value(second.0),
        Some(&Value::Constant(ConstantIndex::from(1_usize)))
    );
    assert_eq!(
        copy.computation(second.2),
        Some(&crate::Computation::Return(second.0))
    );
    assert_eq!(copy.value_type(second.1), Some(&ValueType::unit()));
    assert_eq!(copy.value_support(second.0), plain.value_support(second.0));
    assert_eq!(
        frozen.value(second.0),
        None,
        "the frozen arena never sees the clone's nodes"
    );

    copy.freeze();
    assert_eq!(
        plain, copy,
        "a second freeze keeps the rows on both sides of the first"
    );
    let before = copy.clone();
    assert!(shares(&before, &copy));
    let third = round(&mut plain, 2, Some(BaseType::Integer));
    assert_eq!(third, round(&mut copy, 2, Some(BaseType::Integer)));

    let past = before.watermark();
    plain.truncate_to(past);
    copy.truncate_to(past);
    assert_eq!(plain, copy, "a truncation past the frozen rows");
    assert_eq!(copy.value(third.0), None);
    plain.truncate_to(mark);
    copy.truncate_to(mark);
    assert_eq!(plain, copy, "a truncation into them");
    assert_eq!(copy.value(second.0), None);
    assert_eq!(
        before.value(second.0),
        Some(&Value::Constant(ConstantIndex::from(1_usize))),
        "and a clone taken before keeps its nodes"
    );
    let again = round(&mut plain, 3, None);
    assert_eq!(
        again,
        round(&mut copy, 3, None),
        "a truncated index is minted again"
    );
    assert_eq!(plain, copy);
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

/// One row of the carried-support witness: its reading, the intuitionistic
/// and linear indices expected, and the support the node carries.
type Expected<'reading> = (&'reading str, Vec<u32>, Vec<u32>, Option<Thinning>);

#[test]
fn every_binder_former_carries_its_bodys_support_past_its_binders()
{
    let mut arena = CoreArena::new();
    let int = Zone::Intuitionistic;
    let variable = |arena: &mut CoreArena, index: u32| {
        arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index))
    };
    // `return (x₀, …)` over the variables `indices` of `zone`.
    let returning = |arena: &mut CoreArena, zone: Zone, indices: &[u32]| {
        let components: Vec<ValueId> = indices
            .iter()
            .map(|&index| arena.value_variable(zone, DeBruijnIndex::from(index)))
            .collect();
        let tuple = arena.value_tuple(&components);
        arena.computation_return(tuple)
    };
    // The indices a support selects in `zone`, raw; none for a dangling read.
    let selected = |support: Option<&Thinning>, zone: Zone| -> Vec<u32> {
        support.map_or_else(Vec::new, |support| {
            support.indices(zone).map(u32::from).collect()
        })
    };
    let mut cases: Vec<Expected<'_>> = Vec::new();

    // λ. return (#0, #2): the binder drops and #2 lowers past it.
    let body = returning(&mut arena, int, &[0, 2]);
    let lambda = arena.computation_lambda(body);
    cases.push((
        "a lambda",
        vec![1],
        vec![],
        arena
            .computation_support(lambda)
            .map(ThinningRef::to_thinning),
    ));
    // λ. return #3: a body ignoring its binder still lowers past it.
    let body = returning(&mut arena, int, &[3]);
    let ignoring = arena.computation_lambda(body);
    cases.push((
        "an unused binder",
        vec![2],
        vec![],
        arena
            .computation_support(ignoring)
            .map(ThinningRef::to_thinning),
    ));
    // bind (return #1) (return (#0, #3)): the continuation alone crosses.
    let bound = returning(&mut arena, int, &[1]);
    let body = returning(&mut arena, int, &[0, 3]);
    let bind = arena.computation_bind(bound, body);
    cases.push((
        "a bind",
        vec![1, 2],
        vec![],
        arena
            .computation_support(bind)
            .map(ThinningRef::to_thinning),
    ));
    // case #0 of [return #0, return #2]: each branch crosses one binder.
    let scrutinee = variable(&mut arena, 0);
    let left = returning(&mut arena, int, &[0]);
    let right = returning(&mut arena, int, &[2]);
    let case = arena.computation_case(scrutinee, &[left, right]);
    cases.push((
        "a case",
        vec![0, 1],
        vec![],
        arena
            .computation_support(case)
            .map(ThinningRef::to_thinning),
    ));
    // split #4 into two, then return (#0, #1, #3): the body crosses both.
    let scrutinee = variable(&mut arena, 4);
    let body = returning(&mut arena, int, &[0, 1, 3]);
    let split = arena.computation_split(scrutinee, ComponentCount::from(2_usize), body);
    cases.push((
        "a split",
        vec![1, 4],
        vec![],
        arena
            .computation_support(split)
            .map(ThinningRef::to_thinning),
    ));
    // fold #5 with [] and (h t ↦ return (#1, #3)): the cell branch crosses two.
    let integer = arena.value_type_base(BaseType::Integer);
    let list = variable(&mut arena, 5);
    let on_nil = returning(&mut arena, int, &[]);
    let on_cons = returning(&mut arena, int, &[1, 3]);
    let fold = arena.computation_list_fold(integer, integer, list, on_nil, on_cons);
    cases.push((
        "a fold",
        vec![1, 5],
        vec![],
        arena
            .computation_support(fold)
            .map(ThinningRef::to_thinning),
    ));
    // reify [apply #0, bind (return #2)]: the bind frame crosses one.
    let argument = variable(&mut arena, 0);
    let continuation = returning(&mut arena, int, &[2]);
    let stack = arena.value_reify(alloc::sync::Arc::from([
        StackFrame::Apply(argument),
        StackFrame::Bind(continuation),
    ]));
    cases.push((
        "a reified stack",
        vec![0, 1],
        vec![],
        arena.value_support(stack).map(ThinningRef::to_thinning),
    ));
    // Λ. #1: a static lambda's body crosses one.
    let one = variable(&mut arena, 1);
    let static_lambda = arena.value_static_lambda(one);
    cases.push((
        "a static lambda",
        vec![0],
        vec![],
        arena
            .value_support(static_lambda)
            .map(ThinningRef::to_thinning),
    ));
    // Σ (El #0) (El #2): the second factor crosses one.
    let code = variable(&mut arena, 0);
    let first = arena.value_type_element(code, Level::zero());
    let code = variable(&mut arena, 2);
    let second = arena.value_type_element(code, Level::zero());
    let sigma = arena.value_type_sigma(first, second);
    cases.push((
        "a sigma",
        vec![0, 1],
        vec![],
        arena
            .value_type_support(sigma)
            .map(ThinningRef::to_thinning),
    ));
    // U (Π (_ : El #3). El #0 → F (El #2)): the domain's #3 stays, the
    // codomain's #0 is the Π's binder and its #2 is the subject's #1.
    let code = variable(&mut arena, 3);
    let domain = arena.value_type_element(code, Level::zero());
    let code = variable(&mut arena, 0);
    let argument = arena.value_type_element(code, Level::zero());
    let code = variable(&mut arena, 2);
    let result = arena.value_type_element(code, Level::zero());
    let result = arena.comp_type_returner(result);
    let codomain = arena.comp_type_arrow(argument, result);
    let pi = arena.comp_type_pi(domain, codomain);
    let dependent = arena.value_type_thunk(pi);
    cases.push((
        "a pi",
        vec![1, 3],
        vec![],
        arena
            .value_type_support(dependent)
            .map(ThinningRef::to_thinning),
    ));
    // El #1 × El #1 × El #0: a repeat is one member.
    let factors: Vec<_> = [1_u32, 1, 0]
        .into_iter()
        .map(|index| {
            let code = variable(&mut arena, index);
            arena.value_type_element(code, Level::zero())
        })
        .collect();
    let repeated = arena.value_type_product(&factors);
    cases.push((
        "a repeat",
        vec![0, 1],
        vec![],
        arena
            .value_type_support(repeated)
            .map(ThinningRef::to_thinning),
    ));
    cases.push((
        "a closed type",
        vec![],
        vec![],
        arena
            .value_type_support(integer)
            .map(ThinningRef::to_thinning),
    ));
    // fork (c : 1) { close(c) } as d ; send(d, #2): each half crosses one
    // linear binder and the intuitionistic #2 crosses none.
    let protocol = arena.value_type_unit();
    let child = arena.computation_session(SessionAction::Close {
        endpoint: DeBruijnIndex::from(0_u32),
    });
    let payload = variable(&mut arena, 2);
    let parent = arena.computation_session(SessionAction::Send {
        endpoint: DeBruijnIndex::from(1_u32),
        payload,
    });
    let fork = arena.computation_session(SessionAction::Fork {
        protocol,
        child,
        parent,
    });
    cases.push((
        "a fork",
        vec![2],
        vec![0],
        arena
            .computation_support(fork)
            .map(ThinningRef::to_thinning),
    ));
    // hold x = #0 ; access x as w { resume(w, #1) } unwind { abort(ℓ1) }: the
    // access names its held slot, its body crosses the view's linear binder
    // and its unwind crosses none; the hold's body crosses one linear binder.
    let written = variable(&mut arena, 1);
    let resumed = arena.computation_memory(MemoryForm::Resume {
        view: DeBruijnIndex::from(0_u32),
        value: written,
    });
    let aborted = arena.computation_memory(MemoryForm::Abort {
        view: DeBruijnIndex::from(1_u32),
    });
    let access = arena.computation_memory(MemoryForm::Access {
        mode: AccessMode::Exclusive { unwind: aborted },
        held: DeBruijnIndex::from(0_u32),
        place: crate::memory::Place::Whole,
        body: resumed,
    });
    cases.push((
        "an access",
        vec![1],
        vec![0, 1],
        arena
            .computation_support(access)
            .map(ThinningRef::to_thinning),
    ));
    let held = variable(&mut arena, 0);
    let hold = arena.computation_memory(MemoryForm::Hold {
        value: held,
        body: access,
        grade: crate::memory::HoldGrade::Many,
    });
    cases.push((
        "a hold",
        vec![0, 1],
        vec![0],
        arena
            .computation_support(hold)
            .map(ThinningRef::to_thinning),
    ));

    for (reading, intuitionistic, linear, support) in cases {
        assert_eq!(
            intuitionistic,
            selected(support.as_ref(), Zone::Intuitionistic),
            "{reading}: intuitionistic"
        );
        assert_eq!(
            linear,
            selected(support.as_ref(), Zone::Linear),
            "{reading}: linear"
        );
    }
    assert!(
        arena.value_support(ValueId(u32::MAX)).is_none(),
        "a dangling id carries nothing"
    );
    // Truncation drops a node's support with it: the re-minted node carries
    // its own, not the one at its index before.
    let mark = arena.watermark();
    let wide = variable(&mut arena, 9);
    arena.truncate_to(mark);
    assert!(
        arena.value_support(wide).is_none(),
        "a truncated node carries nothing"
    );
    let closed = arena.value_unit();
    assert_eq!(wide, closed, "the slot is reused");
    assert_eq!(
        Vec::<u32>::new(),
        selected(
            arena
                .value_support(closed)
                .map(ThinningRef::to_thinning)
                .as_ref(),
            Zone::Intuitionistic
        )
    );
}

/// A support wider than a slot is kept in the arena's words and read back
/// whole, a support in both zones reads back in both, and truncation drops
/// the words with their node and keeps every node before the mark.
#[test]
fn a_wide_support_is_kept_in_the_word_arena()
{
    let mut arena = CoreArena::new();
    let int = Zone::Intuitionistic;
    let at = DeBruijnIndex::from;
    let owned = |support: Option<ThinningRef<'_>>| support.map(ThinningRef::to_thinning);
    let near = arena.value_variable(int, at(3));
    let deep = arena.value_variable(Zone::Linear, at(5000));
    let pair = arena.value_tuple(&[near, deep]);
    assert_eq!(
        owned(arena.value_support(pair)),
        Some(Thinning::from_ascending(&[at(3)], &[at(5000)]).expect("ascending"))
    );
    let mark = arena.watermark();
    let words = arena.words.mark();
    let scattered = [0_u32, 100, 5000, 9000, 20000, 40000];
    let components: Vec<ValueId> = scattered
        .iter()
        .map(|&index| arena.value_variable(int, at(index)))
        .collect();
    let wide = arena.value_tuple(&components);
    let expected = Thinning::from_ascending(&scattered.map(at), &[]).expect("ascending");
    assert!(
        usize::from(expected.view().words()) > 1,
        "the code spans words"
    );
    assert!(
        arena.words.mark() > words,
        "the wide code takes the word arena"
    );
    assert_eq!(owned(arena.value_support(wide)), Some(expected));
    arena.truncate_to(mark);
    assert_eq!(arena.words.mark(), words, "the wide code's words are gone");
    assert!(arena.value_support(wide).is_none());
    assert_eq!(
        owned(arena.value_support(near)),
        Some(Thinning::leaf(int, at(3)))
    );
}
