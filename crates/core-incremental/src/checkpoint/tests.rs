use alloc::collections::BTreeSet;
use alloc::vec;

use gandr_core_checker::Declaration;
use gandr_core_checker::OriginToken;
use gandr_core_checker::body;
use gandr_core_checker::signature;
use gandr_core_term::CoreArena;
use gandr_kernel_strata::Level;
use gandr_kernel_term::ConstantIndex;
use quenchant_shape::shape::Maybe;

use super::AdoptionInput;
use super::Answer;
use super::Answered;
use super::Candidate;
use super::ItemCheckpoint;
use super::Standing;
use super::touches;
use crate::boundary::ItemOrdinal;
use crate::boundary::NodeIndex;
use crate::boundary::Occurrence;
use crate::content::ContentNode;
use crate::content::encode_item;
use crate::content::seating;
use crate::footprint::footprint_of;
use crate::region::Item;
use crate::region::ItemKey;
use crate::region::Program;
use crate::region::Reference;
use crate::typing::Typing;

#[test]
fn recorded_answer_references_participate_in_value_invalidation()
{
    let declaration = Declaration::new(
        ConstantIndex::from(1_usize),
        Maybe::Absent(signature::Absent::Unsigned),
        Maybe::Absent(body::Absent::Hole),
        OriginToken::from(1_usize),
    );
    let program = Program::new(CoreArena::new(), vec![Item::new(
        ItemKey::from("target"),
        declaration,
    )])
    .expect("one position");
    let item = encode_item(
        program.arena(),
        program.layout(),
        ItemOrdinal::from(0_usize),
    );
    let footprint = footprint_of(&item.content);
    assert_eq!(footprint.type_reads().count(), 0_usize);
    let abstract_name = Reference::Item {
        key: ItemKey::from("abstract"),
        occurrence: Occurrence::from(0_usize),
    };
    let code_name = Reference::Item {
        key: ItemKey::from("code"),
        occurrence: Occurrence::from(0_usize),
    };
    let table = crate::fixture::type_content(&[
        ContentNode::Product(vec![NodeIndex::from(1_usize), NodeIndex::from(2_usize)]),
        ContentNode::Abstract(abstract_name.clone()),
        ContentNode::Element {
            code: NodeIndex::from(3_usize),
            target: Level::zero(),
        },
        ContentNode::Constant(code_name.clone()),
    ]);
    let checkpoint = ItemCheckpoint::new(
        item.content.clone(),
        footprint.clone(),
        vec![Answered::new(Reference::Unoccupied, Answer::Typed(table))],
        Typing::Owed,
    );
    let candidate = Candidate {
        checkpoint: &checkpoint,
        seat: Maybe::Absent(seating::Absent::Unseatable),
    };
    let unrelated = Reference::Item {
        key: ItemKey::from("unrelated"),
        occurrence: Occurrence::from(0_usize),
    };
    let untyped = [Answered::new(Reference::Unoccupied, Answer::Untyped)];
    for (name, support, expected) in [
        (&unrelated, checkpoint.support.as_slice(), Standing::Stands),
        (
            &abstract_name,
            checkpoint.support.as_slice(),
            Standing::Falls,
        ),
        (&code_name, checkpoint.support.as_slice(), Standing::Falls),
        (&abstract_name, untyped.as_slice(), Standing::Stands),
    ] {
        let value_changed = BTreeSet::from([name.clone()]);
        let input = AdoptionInput {
            candidate: &candidate,
            item: &item,
            footprint: &footprint,
            declaration: program.items()[0].declaration(),
            layout: program.layout(),
            supplied: &[],
            ordinal: ItemOrdinal::from(0_usize),
            value_changed: &value_changed,
        };
        assert_eq!(touches(&input, support), expected);
    }
    // With no earlier item to answer, a recorded absence stands and a
    // recorded type falls.
    let no_change = BTreeSet::new();
    let input = AdoptionInput {
        candidate: &candidate,
        item: &item,
        footprint: &footprint,
        declaration: program.items()[0].declaration(),
        layout: program.layout(),
        supplied: &[],
        ordinal: ItemOrdinal::from(0_usize),
        value_changed: &no_change,
    };
    for (answer, expected) in [
        (Answer::Untyped, Standing::Stands),
        (Answer::Data(None), Standing::Stands),
        (
            Answer::Typed(crate::fixture::type_content(&[ContentNode::Product(
                Vec::new(),
            )])),
            Standing::Falls,
        ),
    ] {
        assert_eq!(
            super::support_holds(&input, &[Answered::new(Reference::Unoccupied, answer)]),
            expected
        );
    }
}

#[test]
fn census_increment_saturates_at_the_boundary()
{
    for (before, expected) in [
        (0_usize, 1_usize),
        (usize::MAX.saturating_sub(1), usize::MAX),
        (usize::MAX, usize::MAX),
    ] {
        let mut count = crate::boundary::ItemCount::from(before);
        super::bump(&mut count);
        assert_eq!(usize::from(count), expected);
    }
}

#[test]
fn support_canonicalization_keeps_the_first_answer()
{
    let a = Reference::Item {
        key: ItemKey::from("a"),
        occurrence: Occurrence::from(0_usize),
    };
    let b = Reference::Item {
        key: ItemKey::from("b"),
        occurrence: Occurrence::from(0_usize),
    };
    let typed = Answer::Typed(crate::fixture::type_content(&[ContentNode::Product(
        Vec::new(),
    )]));
    let mut support = vec![
        Answered::new(b.clone(), Answer::Untyped),
        Answered::new(a.clone(), typed.clone()),
        Answered::new(b.clone(), typed.clone()),
        Answered::new(a.clone(), Answer::Untyped),
    ];
    let program = crate::fixture::integers(CoreArena::new(), &[(
        crate::fixture::Key("owner"),
        crate::fixture::Digits("1"),
    )]);
    let item = encode_item(
        program.arena(),
        program.layout(),
        ItemOrdinal::from(0_usize),
    );
    let footprint = footprint_of(&item.content);
    let checkpoint = ItemCheckpoint::new(item.content, footprint, support.clone(), Typing::Owed);
    assert_eq!(checkpoint.support(), [
        Answered::new(a.clone(), typed.clone()),
        Answered::new(b.clone(), Answer::Untyped)
    ]);
    support.reverse();
    let checkpoint = checkpoint.with_support(support);
    assert_eq!(checkpoint.support(), [
        Answered::new(a, Answer::Untyped),
        Answered::new(b, typed)
    ]);
    assert_eq!(super::canonical_support(vec![]), vec![]);
}

#[test]
fn revision_handles_track_insertions_and_deletions()
{
    let empty = super::Resume::from_checkpoints(super::Checkpoints::new(
        gandr_core_checker::CheckBudget::DEFAULT,
        vec![],
    ))
    .expect("an empty restored revision");
    let mut original_program = crate::fixture::integers(CoreArena::new(), &[
        (crate::fixture::Key("a"), crate::fixture::Digits("1")),
        (crate::fixture::Key("c"), crate::fixture::Digits("3")),
    ]);
    let original = super::resume(empty, &mut original_program).expect("initial insertion");
    let foreign = *original.handles().first().expect("two items");
    let restored = super::Resume::from_checkpoints(original.checkpoints().clone())
        .expect("restored two-item revision");
    assert_eq!(
        restored.reference(foreign),
        Maybe::Absent(crate::order::handle::Absent::Stale)
    );
    let &[a, c] = restored.handles()
    else {
        panic!("two restored handles");
    };
    let mut inserted_program = crate::fixture::integers(CoreArena::new(), &[
        (crate::fixture::Key("a"), crate::fixture::Digits("1")),
        (crate::fixture::Key("b"), crate::fixture::Digits("2")),
        (crate::fixture::Key("c"), crate::fixture::Digits("3")),
    ]);
    let inserted = super::resume(restored, &mut inserted_program).expect("insert the middle item");
    let &[kept_a, b, kept_c] = inserted.handles()
    else {
        panic!("three handles after insertion");
    };
    assert_eq!((kept_a, kept_c), (a, c));
    assert_eq!(
        inserted.compare(a, b),
        Maybe::Present(core::cmp::Ordering::Less)
    );
    assert_eq!(
        inserted.compare(b, c),
        Maybe::Present(core::cmp::Ordering::Less)
    );
    assert_eq!(
        inserted.reference(c),
        Maybe::Present(&Reference::Item {
            key: ItemKey::from("c"),
            occurrence: Occurrence::from(0_usize)
        })
    );
    let mut deleted_program = crate::fixture::integers(CoreArena::new(), &[
        (crate::fixture::Key("a"), crate::fixture::Digits("1")),
        (crate::fixture::Key("b"), crate::fixture::Digits("2")),
    ]);
    let deleted = super::resume(inserted, &mut deleted_program).expect("delete the final item");
    assert_eq!(deleted.handles(), [a, b]);
    assert_eq!(
        deleted.compare(a, c),
        Maybe::Absent(crate::order::handle::Absent::Stale)
    );
    assert_eq!(
        deleted.compare(c, a),
        Maybe::Absent(crate::order::handle::Absent::Stale)
    );
    assert_eq!(
        deleted.reference(c),
        Maybe::Absent(crate::order::handle::Absent::Stale)
    );
    assert_eq!(
        deleted.compare(b, a),
        Maybe::Present(core::cmp::Ordering::Greater)
    );
    assert_eq!(
        deleted.compare(b, b),
        Maybe::Present(core::cmp::Ordering::Equal)
    );
}

#[test]
fn value_change_closure_handles_cycles_and_opaque_readers()
{
    let mut foreign_arena = CoreArena::new();
    let foreign = core::iter::repeat_with(|| foreign_arena.value_unit())
        .take(5_usize)
        .last()
        .expect("five values");
    let program_for = |signed: bool| {
        let mut arena = CoreArena::new();
        let unit = arena.value_type_unit();
        let bodies = [
            arena.value_constant(ConstantIndex::from(1_usize)),
            arena.value_constant(ConstantIndex::from(0_usize)),
            foreign,
            arena.value_constant(ConstantIndex::from(2_usize)),
            arena.value_unit(),
        ];
        let items = ["a", "b", "opaque", "reader", "bystander"]
            .into_iter()
            .zip(bodies)
            .enumerate()
            .map(|(position, (key, body))| {
                Item::new(
                    ItemKey::from(key),
                    Declaration::new(
                        ConstantIndex::from(position),
                        if signed && position == 0 {
                            Maybe::Present(unit)
                        }
                        else {
                            Maybe::Absent(signature::Absent::Unsigned)
                        },
                        Maybe::Present(body),
                        OriginToken::from(position),
                    ),
                )
            })
            .collect();
        Program::new(arena, items).expect("ascending positions")
    };
    let original = program_for(false);
    let before: alloc::vec::Vec<_> = (0 .. original.items().len())
        .map(|index| {
            encode_item(
                original.arena(),
                original.layout(),
                ItemOrdinal::from(index),
            )
        })
        .collect();
    let footprints: alloc::vec::Vec<_> = before
        .iter()
        .map(|item| footprint_of(&item.content))
        .collect();
    let base = super::Checkpoints::new(
        gandr_core_checker::CheckBudget::DEFAULT,
        before
            .iter()
            .zip(&footprints)
            .map(|(item, footprint)| {
                ItemCheckpoint::new(
                    item.content.clone(),
                    footprint.clone(),
                    vec![],
                    Typing::Owed,
                )
            })
            .collect(),
    );
    let mut census = super::ResumeCensus::default();
    assert_eq!(
        super::close_value_changes(&base, &before, &footprints, &mut census),
        BTreeSet::new()
    );
    assert_eq!(census, super::ResumeCensus::default());
    let edited = program_for(true);
    let after: alloc::vec::Vec<_> = (0 .. edited.items().len())
        .map(|index| encode_item(edited.arena(), edited.layout(), ItemOrdinal::from(index)))
        .collect();
    let footprints: alloc::vec::Vec<_> = after
        .iter()
        .map(|item| footprint_of(&item.content))
        .collect();
    let changed = super::close_value_changes(&base, &after, &footprints, &mut census);
    let expected = ["a", "b", "opaque", "reader"]
        .into_iter()
        .map(|key| Reference::Item {
            key: ItemKey::from(key),
            occurrence: Occurrence::from(0_usize),
        })
        .collect();
    assert_eq!(changed, expected);
    assert_eq!(usize::from(census.seeds), 1_usize);
    assert_eq!(usize::from(census.value_changed), 4_usize);
    assert_eq!(usize::from(census.closure_edges), 3_usize);
}
