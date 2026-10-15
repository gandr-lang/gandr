use alloc::vec;

use gandr_core_checker::Declaration;
use gandr_core_checker::OriginToken;
use gandr_core_checker::body;
use gandr_core_checker::signature;
use gandr_core_term::CoreArena;
use gandr_kernel_term::ConstantIndex;
use quenchant_shape::shape::Maybe;

use super::Item;
use super::ItemKey;
use super::Program;
use super::ProgramError;
use super::Reference;
use crate::boundary::ItemOrdinal;
use crate::boundary::Occurrence;

/// A fixture item's key text.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Name(&'static str);

/// A fixture item's admission position.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct At(usize);

/// A bodiless, unsigned item named `key` at `position`.
///
/// # Specification
/// trivial.
fn item(
    key: Name,
    position: At,
) -> Item
{
    Item::new(
        ItemKey::from(key.0),
        Declaration::new(
            ConstantIndex::from(position.0),
            Maybe::Absent(signature::Absent::Unsigned),
            Maybe::Absent(body::Absent::Hole),
            OriginToken::from(position.0),
        ),
    )
}

#[test]
fn positions_must_ascend_and_may_skip()
{
    let skipping = Program::new(CoreArena::new(), vec![
        item(Name("a"), At(0)),
        item(Name("b"), At(3)),
    ])
    .expect("a gap is admissible");
    assert_eq!(
        skipping.resolve(ConstantIndex::from(1_usize)),
        Reference::Unoccupied,
        "a skipped position resolves to no item"
    );
    assert_eq!(
        skipping.resolve(ConstantIndex::from(3_usize)),
        Reference::Item {
            key: ItemKey::from("b"),
            occurrence: Occurrence::from(0_usize),
        },
        "an occupied position resolves to its item"
    );
    for (later, label) in [(1_usize, "repeated"), (0_usize, "descending")] {
        assert_eq!(
            Program::new(CoreArena::new(), vec![
                item(Name("a"), At(1)),
                item(Name("b"), At(later))
            ])
            .map(|_| ()),
            Err(ProgramError::PositionOrder {
                ordinal: ItemOrdinal::from(1_usize),
                position: ConstantIndex::from(later),
                previous: ConstantIndex::from(1_usize),
            }),
            "a {label} position is refused with both positions"
        );
    }
}

#[test]
fn a_repeated_key_counts_its_occurrences()
{
    let program = Program::new(CoreArena::new(), vec![
        item(Name("d"), At(0)),
        item(Name("e"), At(1)),
        item(Name("d"), At(2)),
    ])
    .expect("ascending");
    assert_eq!(
        program.references(),
        [
            Reference::Item {
                key: ItemKey::from("d"),
                occurrence: Occurrence::from(0_usize),
            },
            Reference::Item {
                key: ItemKey::from("e"),
                occurrence: Occurrence::from(0_usize),
            },
            Reference::Item {
                key: ItemKey::from("d"),
                occurrence: Occurrence::from(1_usize),
            },
        ],
        "the second item of a key is its first repeat"
    );
    for (index, reference) in program.references().iter().enumerate() {
        assert_eq!(
            program.layout().ordinal_of(reference),
            Maybe::Present(ItemOrdinal::from(index)),
        );
        assert_eq!(program.resolve(ConstantIndex::from(index)), *reference);
    }
    for missing in [
        Reference::Unoccupied,
        Reference::Item {
            key: ItemKey::from("absent"),
            occurrence: Occurrence::from(0_usize),
        },
        Reference::Item {
            key: ItemKey::from("e"),
            occurrence: Occurrence::from(1_usize),
        },
    ] {
        assert_eq!(
            program.layout().ordinal_of(&missing),
            Maybe::Absent(super::naming::Absent::Unnamed),
        );
    }
}

#[test]
fn empty_and_extreme_programs_resolve_exactly()
{
    let empty = Program::new(CoreArena::new(), vec![]).expect("empty program");
    assert_eq!(empty.items(), []);
    assert_eq!(empty.references(), []);
    for position in [0_usize, usize::MAX] {
        assert_eq!(
            empty.resolve(ConstantIndex::from(position)),
            Reference::Unoccupied
        );
    }
    assert_eq!(
        empty.layout().ordinal_of(&Reference::Unoccupied),
        Maybe::Absent(super::naming::Absent::Unnamed),
    );

    let extreme = Program::new(CoreArena::new(), vec![item(Name("edge"), At(usize::MAX))])
        .expect("the maximum position has no predecessor");
    let reference = Reference::Item {
        key: ItemKey::from("edge"),
        occurrence: Occurrence::from(0_usize),
    };
    assert_eq!(extreme.references(), core::slice::from_ref(&reference));
    assert_eq!(extreme.resolve(ConstantIndex::from(usize::MAX)), reference);
    assert_eq!(
        extreme.resolve(ConstantIndex::from(0_usize)),
        Reference::Unoccupied
    );
    assert_eq!(
        extreme.layout().ordinal_of(&reference),
        Maybe::Present(ItemOrdinal::from(0_usize))
    );
}

#[test]
fn the_first_position_violation_wins()
{
    assert_eq!(
        Program::new(CoreArena::new(), vec![
            item(Name("a"), At(0)),
            item(Name("b"), At(4)),
            item(Name("c"), At(4)),
            item(Name("d"), At(2)),
        ])
        .map(|_| ()),
        Err(ProgramError::PositionOrder {
            ordinal: ItemOrdinal::from(2_usize),
            position: ConstantIndex::from(4_usize),
            previous: ConstantIndex::from(4_usize),
        }),
    );
}
