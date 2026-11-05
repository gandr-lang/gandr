use alloc::collections::BTreeMap;
use alloc::vec;
use alloc::vec::Vec;

use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::FieldCount;

use super::ArmCount;
use super::BranchCount;
use super::Cases;
use super::Cover;
use super::CoverRefusal;
use super::Step;
use super::StepId;
use crate::CoreArena;
use crate::syntax::DataSignature;

/// `Nat`, `Maybe` and `List` at constants 0, 1 and 2.
///
/// # Specification
/// trivial.
fn signatures(arena: &mut CoreArena) -> BTreeMap<ConstantIndex, DataSignature>
{
    let universe = arena.value_type_data(ConstantIndex::from(9_usize), vec![]);
    let nat = arena.value_type_data(ConstantIndex::from(0_usize), vec![]);
    let element = arena.value_type_data(ConstantIndex::from(8_usize), vec![]);
    let list = arena.value_type_data(ConstantIndex::from(2_usize), vec![]);
    BTreeMap::from([
        (
            ConstantIndex::from(0_usize),
            DataSignature::new(vec![], vec![vec![], vec![nat]], universe),
        ),
        (
            ConstantIndex::from(1_usize),
            DataSignature::new(vec![universe], vec![vec![], vec![element]], universe),
        ),
        (
            ConstantIndex::from(2_usize),
            DataSignature::new(vec![universe], vec![vec![], vec![element, list]], universe),
        ),
    ])
}

/// A split over `family`'s constructors, each with its field count.
///
/// # Specification
/// trivial.
fn data(
    family: ConstantIndex,
    counts: &[FieldCount],
    branches: Vec<StepId>,
) -> Step
{
    Step::Split {
        cases: Cases::Data {
            family,
            constructors: counts
                .iter()
                .enumerate()
                .map(|(tag, &count)| (ConstructorTag::from(tag), count))
                .collect(),
        },
        branches,
    }
}

/// The derivation the lowering records for a match over `List(Maybe(Nat))`
/// of five arms: `Nil`, `Cons(None, t)`, `Cons(Some(Zero), Nil)`,
/// `Cons(Some(Succ(n)), t)` and `Cons(Some(Zero), Cons(m, t))`.
///
/// # Specification
/// trivial.
fn nested(maybe_counts: &[FieldCount]) -> Cover
{
    let [nat_family, maybe_family, list_family] = [0_usize, 1, 2].map(ConstantIndex::from);
    let mut cover = Cover::new();
    let nil_arm = cover.mint(Step::Var(0));
    let none_arm = cover.mint(Step::Var(1));
    let inner_nil = cover.mint(Step::Var(2));
    let inner_cons = cover.mint(Step::Var(4));
    let inner = cover.mint(data(
        list_family,
        &[0_usize, 2].map(FieldCount::from),
        vec![inner_nil, inner_cons],
    ));
    let zero = cover.mint(Step::Compose(inner));
    let succ = cover.mint(Step::Var(3));
    let nat = cover.mint(data(nat_family, &[0_usize, 1].map(FieldCount::from), vec![
        zero, succ,
    ]));
    let some = cover.mint(Step::Compose(nat));
    let maybe_branches = [none_arm, some][.. maybe_counts.len()].to_vec();
    let maybe = cover.mint(data(maybe_family, maybe_counts, maybe_branches));
    let cons = cover.mint(Step::Compose(maybe));
    cover.mint(data(
        list_family,
        &[0_usize, 2].map(FieldCount::from),
        vec![nil_arm, cons],
    ));
    cover
}

#[test]
fn a_step_names_its_parts_in_order()
{
    let mut cover = Cover::new();
    let left = cover.mint(Step::Var(0));
    let right = cover.mint(Step::Var(1));
    let split = cover.mint(Step::Split {
        cases: Cases::Boolean,
        branches: vec![left, right],
    });
    let composed = cover.mint(Step::Compose(split));
    assert_eq!(cover.step(left).map(Step::parts), Some(&[][..]));
    assert_eq!(cover.step(split).map(Step::parts), Some(&[left, right][..]));
    assert_eq!(cover.step(composed).map(Step::parts), Some(&[split][..]));
    assert_eq!(
        Cover::new().step(left),
        None,
        "an empty derivation names nothing"
    );
}

#[test]
fn each_split_holds_one_branch_per_case()
{
    let three = Cases::Data {
        family: ConstantIndex::from(0_usize),
        constructors: vec![
            (ConstructorTag::from(0_usize), FieldCount::from(0_usize)),
            (ConstructorTag::from(1_usize), FieldCount::from(1_usize)),
            (ConstructorTag::from(2_usize), FieldCount::from(2_usize)),
        ],
    };
    assert_eq!(three.width(), BranchCount::from(3_usize));
    assert_eq!(Cases::Sum(4).width(), BranchCount::from(4_usize));
    assert_eq!(Cases::Absurd.width(), BranchCount::from(0_usize));
    assert_eq!(
        Cases::Tuple(3).width(),
        BranchCount::from(1_usize),
        "a tuple splits under one branch"
    );
}

#[test]
fn a_nested_match_s_derivation_is_admitted()
{
    let mut arena = CoreArena::new();
    let signatures = signatures(&mut arena);
    let cover = nested(&[0_usize, 1].map(FieldCount::from));
    assert_eq!(
        cover.check(ArmCount::from(5_usize), |family| signatures.get(&family)),
        Ok(())
    );
}

#[test]
fn a_split_that_drops_a_constructor_is_refused()
{
    let mut arena = CoreArena::new();
    let signatures = signatures(&mut arena);
    let dropped = nested(&[FieldCount::from(0_usize)]);
    assert!(
        matches!(
            dropped.check(ArmCount::from(5_usize), |family| signatures.get(&family)),
            Err(CoverRefusal::ConstructorCount(_))
        ),
        "`Maybe`'s split without `Some` is refused by name"
    );
}

#[test]
fn each_broken_rule_is_refused_by_its_own_name()
{
    let mut arena = CoreArena::new();
    let signatures = signatures(&mut arena);
    let declared = |family| signatures.get(&family);
    let mut swapped = Cover::new();
    let zero = swapped.mint(Step::Var(0));
    let succ = swapped.mint(Step::Var(1));
    swapped.mint(Step::Split {
        cases: Cases::Data {
            family: ConstantIndex::from(0_usize),
            constructors: vec![
                (ConstructorTag::from(1_usize), FieldCount::from(1_usize)),
                (ConstructorTag::from(0_usize), FieldCount::from(0_usize)),
            ],
        },
        branches: vec![succ, zero],
    });
    let mut miscounted = Cover::new();
    let zero = miscounted.mint(Step::Var(0));
    let succ = miscounted.mint(Step::Var(1));
    miscounted.mint(data(
        ConstantIndex::from(0_usize),
        &[0_usize, 2].map(FieldCount::from),
        vec![zero, succ],
    ));
    let mut unknown = Cover::new();
    let only = unknown.mint(Step::Var(0));
    unknown.mint(data(
        ConstantIndex::from(7_usize),
        &[FieldCount::from(0_usize)],
        vec![only],
    ));
    let mut short = Cover::new();
    let only = short.mint(Step::Var(0));
    short.mint(Step::Split {
        cases: Cases::Boolean,
        branches: vec![only],
    });
    let mut stray = Cover::new();
    stray.mint(Step::Var(2));
    let mut dangling = Cover::new();
    dangling.mint(Step::Compose(StepId(0)));
    for (cover, refusal) in [
        (swapped, CoverRefusal::ConstructorOrder(StepId(2))),
        (miscounted, CoverRefusal::FieldCount(StepId(2))),
        (unknown, CoverRefusal::UnknownFamily(StepId(1))),
        (short, CoverRefusal::BranchCount(StepId(1))),
        (stray, CoverRefusal::UnknownArm(StepId(0))),
        (dangling, CoverRefusal::Dangling(StepId(0))),
        (Cover::new(), CoverRefusal::Empty),
    ] {
        assert_eq!(cover.check(ArmCount::from(2_usize), declared), Err(refusal));
    }
}

#[test]
fn a_derivation_grows_linearly_with_its_tree()
{
    // A chain of `k` nested `Nat` splits holds `3k + 1` steps: one `var`, one
    // composition and one split for each level, and the last `var`.
    let chain = |levels: usize| {
        let mut cover = Cover::new();
        let mut below = cover.mint(Step::Var(0));
        for _ in 0 .. levels {
            let zero = cover.mint(Step::Var(1));
            let succ = cover.mint(Step::Compose(below));
            below = cover.mint(data(
                ConstantIndex::from(0_usize),
                &[0_usize, 1].map(FieldCount::from),
                vec![zero, succ],
            ));
        }
        cover
    };
    let mut arena = CoreArena::new();
    let signatures = signatures(&mut arena);
    for levels in [16_usize, 32_usize] {
        let cover = chain(levels);
        assert_eq!(
            cover.steps().count(),
            levels.saturating_mul(3).saturating_add(1)
        );
        assert_eq!(
            cover.check(ArmCount::from(2_usize), |family| signatures.get(&family)),
            Ok(())
        );
    }
}
