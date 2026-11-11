use alloc::vec;
use alloc::vec::Vec;

use gandr_core_checker::Declaration;
use gandr_core_checker::OriginToken;
use gandr_core_checker::signature;
use gandr_core_term::CoreArena;
use gandr_core_term::effect::EffectRow;
use gandr_kernel_term::ConstantIndex;
use quenchant_shape::shape::Maybe;

use super::Bundle;
use super::SourceKeys;
use super::SourceRun;
use super::SourcesError;
use super::unheld;
use super::unkeyed;
use crate::boundary::ItemCount;
use crate::boundary::SourceOrdinal;
use crate::fixture::Digits;
use crate::fixture::Key;
use crate::fixture::Position;
use crate::fixture::checked;
use crate::fixture::declaration;
use crate::fixture::integer;
use crate::region::Item;
use crate::region::ItemKey;
use crate::region::Program;

/// What a fixture item declares.
#[derive(Clone, Copy, Debug)]
enum Body
{
    /// An integer literal.
    Digits(Digits),
    /// The item at an earlier position.
    Names(Position),
    /// A world, which locates the item and makes it opaque.
    World,
}

/// The program of `entries`, each an item's key and what it declares, at
/// positions from zero in order.
///
/// # Specification
/// trivial.
fn program(entries: &[(Key, Body)]) -> Program
{
    let mut arena = CoreArena::new();
    let items = entries
        .iter()
        .enumerate()
        .map(|(position, &(key, body))| {
            let unsigned = Maybe::Absent(signature::Absent::Unsigned);
            let declared = match body {
                Body::Digits(digits) => {
                    let literal = arena.value_literal(integer(digits));
                    declaration(Position(position), unsigned, Maybe::Present(literal))
                },
                Body::Names(named) => {
                    let constant = arena.value_constant(ConstantIndex::from(named.0));
                    declaration(Position(position), unsigned, Maybe::Present(constant))
                },
                Body::World => Declaration::world(
                    ConstantIndex::from(position),
                    EffectRow::EMPTY,
                    OriginToken::from(position),
                ),
            };
            Item::new(ItemKey::from(key.0), declared)
        })
        .collect();
    Program::new(arena, items).expect("positions ascend")
}

/// A source of `items` items that imports the sources at `imports`.
///
/// # Specification
/// trivial.
fn run(
    items: Position,
    imports: &[Position],
) -> SourceRun
{
    SourceRun::new(
        ItemCount::from(items.0),
        imports
            .iter()
            .map(|&import| SourceOrdinal::from(import.0))
            .collect(),
    )
}

/// #6512: a closure `R` imports `C`, then `S`, and `S` imports `B`, then
/// `C`. The closure lays `C` before `B`, and `S`'s own closure lays `B`
/// before `C`. The bundle of `R`'s set restricts by `S`'s keys to the set that
/// a fresh check of `S`'s closure gives, in `S`'s own order.
#[test]
fn a_set_restricts_to_the_fresh_set_of_a_closure_inside_it_6512()
{
    let mut whole = program(&[
        (Key("c"), Body::Digits(Digits("3"))),
        (Key("b"), Body::Digits(Digits("2"))),
        (Key("s"), Body::Names(Position(1))),
        (Key("t"), Body::Names(Position(0))),
        (Key("r"), Body::Names(Position(2))),
    ]);
    let laid = [
        run(Position(1), &[]),
        run(Position(1), &[]),
        run(Position(2), &[Position(1), Position(0)]),
        run(Position(1), &[Position(0), Position(2)]),
    ];
    let bundle = Bundle::of(&checked(&mut whole), &laid).expect("the sources lay the set out");
    let mut inside = program(&[
        (Key("b"), Body::Digits(Digits("2"))),
        (Key("c"), Body::Digits(Digits("3"))),
        (Key("s"), Body::Names(Position(0))),
        (Key("t"), Body::Names(Position(1))),
    ]);
    let keys = SourceKeys::of(&inside, &[
        run(Position(1), &[]),
        run(Position(1), &[]),
        run(Position(2), &[Position(0), Position(1)]),
    ])
    .expect("the sources lay the program out");
    assert_eq!(
        bundle.restrict(&keys),
        Maybe::Present(checked(&mut inside)),
        "the restriction is the fresh set of the closure inside"
    );
}

/// #6512: a source's key digests the keys of what it imports, so one source
/// over another import takes another key, and the bundle holds no run for
/// it. Sources that import forward, or that lay out other items than the
/// program holds, are refused by name.
#[test]
fn a_source_s_key_moves_with_what_it_imports_6512()
{
    let laid = [run(Position(1), &[]), run(Position(1), &[Position(0)])];
    let over = |digits: Digits| {
        program(&[
            (Key("a"), Body::Digits(digits)),
            (Key("b"), Body::Names(Position(0))),
        ])
    };
    let (mut before, after) = (over(Digits("1")), over(Digits("2")));
    let (old, new) = (
        SourceKeys::of(&before, &laid).expect("the sources lay the program out"),
        SourceKeys::of(&after, &laid).expect("the sources lay the program out"),
    );
    assert!(
        old.keys()
            .iter()
            .zip(new.keys())
            .all(|(old, new)| old != new),
        "the edited source and the source over it each take another key: {old:?} {new:?}"
    );
    let bundle = Bundle::of(&checked(&mut before), &laid).expect("the sources lay the set out");
    assert_eq!(bundle.restrict(&new), Maybe::Absent(unheld::Absent::Unheld));
    assert_eq!(
        SourceKeys::of(&after, &[
            run(Position(1), &[Position(1)]),
            run(Position(1), &[])
        ]),
        Err(SourcesError::Forward {
            source: SourceOrdinal::from(0_usize),
            import: SourceOrdinal::from(1_usize),
        })
    );
    assert_eq!(
        SourceKeys::of(&after, &[run(Position(1), &[])]),
        Err(SourcesError::Uncovered {
            runs: ItemCount::from(1_usize),
            items: ItemCount::from(2_usize),
        })
    );
}

/// #6512: a world is opaque, so its source has no key, and the source that
/// imports it has none. The bundle holds the run of the source beside them,
/// and gives no set for a closure that holds the world.
#[test]
fn a_closure_with_an_opaque_source_restricts_to_nothing_6512()
{
    let mut located = program(&[
        (Key("w"), Body::World),
        (Key("b"), Body::Digits(Digits("1"))),
        (Key("c"), Body::Digits(Digits("2"))),
    ]);
    let laid = [
        run(Position(1), &[]),
        run(Position(1), &[Position(0)]),
        run(Position(1), &[]),
    ];
    let keys = SourceKeys::of(&located, &laid).expect("the sources lay the program out");
    let reasons: Vec<Maybe<(), unkeyed::Absent>> =
        keys.keys().iter().map(|key| key.map(|_| ())).collect();
    assert_eq!(reasons, vec![
        Maybe::Absent(unkeyed::Absent::Opaque),
        Maybe::Absent(unkeyed::Absent::Reaches),
        Maybe::Present(()),
    ]);
    let bundle = Bundle::of(&checked(&mut located), &laid).expect("the sources lay the set out");
    assert_eq!(
        bundle.restrict(&keys),
        Maybe::Absent(unheld::Absent::Unkeyed)
    );
    let mut beside = program(&[(Key("c"), Body::Digits(Digits("2")))]);
    let alone =
        SourceKeys::of(&beside, &[run(Position(1), &[])]).expect("the source lays the program out");
    assert_eq!(
        bundle.restrict(&alone),
        Maybe::Present(checked(&mut beside)),
        "the run beside the world restricts to its own fresh set"
    );
}
