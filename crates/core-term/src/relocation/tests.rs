use gandr_kernel_term::DeBruijnIndex;
use quenchant_shape::shape::Maybe;

use super::Offset;
use super::Relocation;
use super::folding;
use crate::arena::CoreArena;
use crate::rewrite::Binders;
use crate::support::Thinning;
use crate::syntax::Zone;

/// The support selecting the intuitionistic `indices`.
///
/// # Specification
/// trivial.
fn support(indices: &[DeBruijnIndex]) -> Thinning
{
    Thinning::from_ascending(indices, &[]).expect("ascending")
}

/// The raise by `amount` at `cutoff`.
///
/// # Specification
/// trivial.
fn raise(
    amount: Binders,
    cutoff: Binders,
) -> Relocation
{
    match Relocation::raise(amount, cutoff) {
        Maybe::Present(relocation) => relocation,
        Maybe::Absent(reason) => panic!("a small raise is held: {reason:?}"),
    }
}

/// The lowering past `past` binders.
///
/// # Specification
/// trivial.
fn lowering(past: Binders) -> Relocation
{
    match Relocation::lowering(past) {
        Maybe::Present(relocation) => relocation,
        Maybe::Absent(reason) => panic!("a small lowering is held: {reason:?}"),
    }
}

#[test]
fn a_relocation_moves_only_intuitionistic_indices_past_its_cutoff()
{
    let index = |raw: u32| DeBruijnIndex::from(raw);
    let binders = |raw: u32| Binders::from(raw);
    let up = raise(binders(2), binders(1));
    assert_eq!(
        up.variable(Zone::Intuitionistic, index(0)),
        index(0),
        "below the cutoff stays"
    );
    assert_eq!(
        up.variable(Zone::Intuitionistic, index(1)),
        index(3),
        "the cutoff moves"
    );
    assert_eq!(
        up.variable(Zone::Intuitionistic, index(4)),
        index(6),
        "past it moves"
    );
    assert_eq!(
        up.variable(Zone::Linear, index(4)),
        index(4),
        "the linear zone stays"
    );
    let down = lowering(binders(2));
    assert_eq!(down.variable(Zone::Intuitionistic, index(1)), index(1));
    assert_eq!(down.variable(Zone::Intuitionistic, index(5)), index(3));
    assert_eq!(
        Offset::lower(Binders::from(3_u32)).moved(Binders::from(1_u32)),
        Binders::NONE,
        "a move below zero clamps"
    );
    assert_eq!(
        Offset::raise(Binders::from(u32::MAX)).moved(Binders::from(1_u32)),
        Binders::from(u32::MAX),
        "a move past the ceiling clamps"
    );
    let under = up.under(Binders::ONE);
    assert_eq!(
        under.cutoff(),
        Binders::from(2_u32),
        "a child reads the cutoff one deeper"
    );
    assert_eq!(
        under.variable(Zone::Intuitionistic, index(1)),
        index(1),
        "its own binder stays"
    );
    assert_eq!(under.variable(Zone::Intuitionistic, index(2)), index(4));
    assert_eq!(up.under(Binders::NONE), up);
    assert_eq!(
        Relocation::IDENTITY.under(Binders::ONE),
        Relocation::IDENTITY,
        "the identity stays the identity under a binder"
    );
    assert_eq!(
        Relocation::raise(Binders::NONE, Binders::ONE),
        Maybe::Present(Relocation::IDENTITY),
        "raising by nothing is the identity"
    );
    assert_eq!(
        Relocation::raise(Binders::from(u32::MAX), Binders::NONE),
        Maybe::Absent(folding::Absent::Wide),
        "an offset past i32 is not held"
    );
}

#[test]
fn a_relocation_fits_to_its_support()
{
    let index = |raw: u32| DeBruijnIndex::from(raw);
    let binders = |raw: u32| Binders::from(raw);
    let up = raise(binders(1), binders(1));
    assert_eq!(
        up.fitted(support(&[]).view()),
        Relocation::IDENTITY,
        "a closed node moves nothing"
    );
    assert_eq!(
        up.fitted(support(&[index(0)]).view()),
        Relocation::IDENTITY,
        "below the cutoff"
    );
    assert_eq!(up.fitted(support(&[index(1)]).view()), up, "at the cutoff");
    assert_eq!(
        up.fitted(support(&[index(0), index(4)]).view()),
        raise(binders(1), binders(4)),
        "the cutoff rises to the least index moved"
    );
    assert_eq!(
        lowering(binders(1)).fitted(support(&[index(3), index(6)]).view()),
        Relocation {
            offset: -1_i32,
            cutoff: Binders::from(3_u32),
        },
        "a lowering fits as a raise does"
    );
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(gandr_kernel_term::BaseType::Integer);
    let open = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(2_u32));
    let decode = arena.value_type_element(open, gandr_kernel_strata::Level::zero());
    assert_eq!(
        arena.place_value_type(integer, up).relocation(),
        Relocation::IDENTITY,
        "a closed type is placed plain"
    );
    assert_eq!(
        arena.place_value_type(decode, up).relocation(),
        raise(binders(1), binders(2)),
        "an open one at its least moved index"
    );
    assert_eq!(arena.place_value(open, up).node(), open);
}

#[test]
fn relocations_fold_exactly_when_the_support_moves_in_one_step()
{
    let index = |raw: u32| DeBruijnIndex::from(raw);
    let binders = |raw: u32| Binders::from(raw);
    let twice = support(&[index(0), index(3)]);
    let first = raise(binders(1), binders(0)).fitted(twice.view());
    assert_eq!(
        first.then(raise(binders(1), binders(2)), twice.view()),
        Maybe::Absent(folding::Absent::Apart),
        "0 moves to 1 and 3 to 5: two offsets"
    );
    let far = support(&[index(3)]);
    assert_eq!(
        raise(binders(1), binders(0))
            .fitted(far.view())
            .then(raise(binders(1), binders(2)), far.view()),
        Maybe::Present(raise(binders(2), binders(3))),
        "one index moves once"
    );
    let near = support(&[index(0)]);
    assert_eq!(
        raise(binders(1), binders(0)).then(raise(binders(1), binders(2)), near.view()),
        Maybe::Present(raise(binders(1), binders(0))),
        "the second raise starts past where the first left 0"
    );
    assert_eq!(
        raise(binders(2), binders(0))
            .fitted(near.view())
            .then(lowering(binders(2)), near.view()),
        Maybe::Present(Relocation::IDENTITY),
        "a raise undone by a lowering is the identity"
    );
    assert_eq!(
        raise(binders(1), binders(0)).then(raise(binders(1), binders(0)), support(&[]).view()),
        Maybe::Present(Relocation::IDENTITY),
        "a closed node folds to the identity"
    );
    assert_eq!(lowering(binders(0)), Relocation::IDENTITY);
    assert_eq!(lowering(binders(2)).cutoff(), Binders::from(2_u32));
}
