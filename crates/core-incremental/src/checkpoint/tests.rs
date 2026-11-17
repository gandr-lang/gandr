use alloc::collections::BTreeSet;
use alloc::vec;

use gandr_core_checker::Declaration;
use gandr_core_checker::OriginToken;
use gandr_core_checker::body;
use gandr_core_checker::signature;
use gandr_core_content::ContentNode;
use gandr_core_content::ItemKey;
use gandr_core_content::NodeIndex;
use gandr_core_content::Occurrence;
use gandr_core_content::Reference;
use gandr_core_content::seating;
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
use super::Supplied;
use super::content_key;
use super::touches;
use crate::boundary::ItemOrdinal;
use crate::content::encode_item;
use crate::fixture::Digits;
use crate::fixture::Key;
use crate::fixture::Noise;
use crate::fixture::integers;
use crate::fixture::noisy;
use crate::footprint::footprint_of;
use crate::region::Item;
use crate::region::Program;
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
        gandr_core_checker::Entered::AsWritten,
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
    let none = Supplied {
        leading: &[],
        own: Vec::new(),
    };
    for (name, support, expected) in [
        (&unrelated, checkpoint.support(), Standing::Stands),
        (&abstract_name, checkpoint.support(), Standing::Falls),
        (&code_name, checkpoint.support(), Standing::Falls),
        (&abstract_name, untyped.as_slice(), Standing::Stands),
    ] {
        let value_changed = BTreeSet::from([name.clone()]);
        let input = AdoptionInput {
            candidate: &candidate,
            item: &item,
            footprint: &footprint,
            declaration: program.items()[0].declaration(),
            layout: program.layout(),
            supplied: &none,
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
        supplied: &none,
        ordinal: ItemOrdinal::from(0_usize),
        value_changed: &no_change,
    };
    let mut arena = program.arena().clone();
    let context = gandr_core_checker::CheckingContext::new(
        &mut arena,
        gandr_core_checker::CheckBudget::DEFAULT,
    );
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
            super::support_holds(
                &context,
                input.reader(),
                &[Answered::new(Reference::Unoccupied, answer)],
                super::Uncompared::Falls
            ),
            expected
        );
    }
}

/// A take whose pass holds another answer of an earlier item than the answer
/// that the judgement read of it fails the requires clause of the take, and the
/// enforcing build refuses it.
#[cfg(anodized_panic)]
#[test]
#[should_panic(expected = "precondition failed")]
fn a_take_past_another_answer_than_the_judgement_read_panics_6727()
{
    // `source = 0`, then `reader = source`: the judgement reads the type
    // `Integer` of `source` for `reader`.
    let unsigned = || Maybe::Absent(signature::Absent::Unsigned);
    let mut arena = CoreArena::new();
    let literal = arena.value_literal(crate::fixture::integer(Digits("0")));
    let named = arena.value_constant(ConstantIndex::from(0_usize));
    let program = Program::new(arena, vec![
        Item::new(
            ItemKey::from("source"),
            crate::fixture::declaration(
                crate::fixture::Position(0),
                unsigned(),
                Maybe::Present(literal),
            ),
        ),
        Item::new(
            ItemKey::from("reader"),
            crate::fixture::declaration(
                crate::fixture::Position(1),
                unsigned(),
                Maybe::Present(named),
            ),
        ),
    ])
    .expect("positions ascend");
    let mut judged = program.arena().clone();
    let mut run = gandr_core_checker::ModuleRun::new();
    run.keep_supports();
    let report = {
        let mut context = gandr_core_checker::CheckingContext::new(
            &mut judged,
            gandr_core_checker::CheckBudget::DEFAULT,
        );
        run.judge(&mut context, &program.declarations(), |_, _, _| {});
        run.finish(&mut context)
    };
    let judgement = super::Judgement::new(&judged, &report);
    // The pass holds `source` untyped, as a pass that refuses it holds it.
    let supplied = Supplied {
        leading: &[],
        own: vec![Answer::Untyped],
    };
    let mut arena = program.arena().clone();
    let mut context = gandr_core_checker::CheckingContext::new(
        &mut arena,
        gandr_core_checker::CheckBudget::DEFAULT,
    );
    let ordinal = ItemOrdinal::from(1_usize);
    let item = encode_item(program.arena(), program.layout(), ordinal);
    let types = gandr_core_content::TypeMemo::default();
    let _taken = judgement.take(&mut context, &super::Taking {
        item: &item,
        declaration: program.items()[1].declaration(),
        layout: program.layout(),
        types: &types,
        supplied: &supplied,
        ordinal,
    });
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
    let checkpoint = ItemCheckpoint::new(
        item.content,
        footprint,
        support.clone(),
        Typing::Owed,
        gandr_core_checker::Entered::AsWritten,
    );
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
                    gandr_core_checker::Entered::AsWritten,
                )
            })
            .collect(),
    );
    let mut census = super::ResumeCensus::default();
    assert_eq!(
        super::close_value_changes(&base.items, &before, &footprints, &mut census),
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
    let changed = super::close_value_changes(&base.items, &after, &footprints, &mut census);
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

/// #1547: an item's content key moves with its content and nothing else: two
/// revisions over arenas numbered apart agree on the key of the item they both
/// hold alike and differ on the one edited between them.
#[test]
fn an_item_s_content_key_moves_only_with_its_content_1547()
{
    let keys = |program: &Program| {
        [0_usize, 1_usize].map(|index| content_key(program, ItemOrdinal::from(index)))
    };
    let first = keys(&integers(CoreArena::new(), &[
        (Key("one"), Digits("1")),
        (Key("two"), Digits("2")),
    ]));
    let edited = keys(&integers(noisy(Noise(3)), &[
        (Key("one"), Digits("1")),
        (Key("two"), Digits("20")),
    ]));
    let (
        [Maybe::Present(first_one), Maybe::Present(first_two)],
        [Maybe::Present(edited_one), Maybe::Present(edited_two)],
    ) = (first, edited)
    else {
        panic!("each integer item has a key: {first:?} {edited:?}");
    };
    assert_eq!(
        first_one, edited_one,
        "the item both revisions hold alike keeps its key over an arena numbered apart"
    );
    assert_ne!(first_two, edited_two, "the edited item's key moves");
}

/// #7403: a node's content key moves with its content and nothing else. The
/// bodies of two items that hold one literal are two nodes of one content,
/// and they share a key, in one arena and over an arena numbered apart. The
/// key of an edited literal moves.
#[test]
fn a_node_s_key_moves_only_with_its_content_7403()
{
    let bodies = |program: &Program| {
        program
            .items()
            .iter()
            .map(|item| match *item.declaration().content() {
                gandr_core_checker::DeclarationContent::Value {
                    body: Maybe::Present(body),
                    ..
                } => (
                    body,
                    super::node_key(
                        (program.arena(), program.layout()),
                        gandr_core_content::ArenaNode::Value(body),
                    ),
                ),
                gandr_core_checker::DeclarationContent::Value { .. }
                | gandr_core_checker::DeclarationContent::Data(_)
                | gandr_core_checker::DeclarationContent::Codata(_)
                | gandr_core_checker::DeclarationContent::Abstract(_)
                | gandr_core_checker::DeclarationContent::World(_) => {
                    panic!("each integer item has a body")
                },
            })
            .collect::<vec::Vec<_>>()
    };
    let first = bodies(&integers(CoreArena::new(), &[
        (Key("one"), Digits("1")),
        (Key("also"), Digits("1")),
        (Key("two"), Digits("2")),
    ]));
    let edited = bodies(&integers(noisy(Noise(3)), &[
        (Key("one"), Digits("1")),
        (Key("also"), Digits("1")),
        (Key("two"), Digits("20")),
    ]));
    let (
        &[
            (one_node, Maybe::Present(one)),
            (also_node, Maybe::Present(also)),
            (_, Maybe::Present(two)),
        ],
        &[
            (edited_node, Maybe::Present(edited_one)),
            _,
            (_, Maybe::Present(edited_two)),
        ],
    ) = (first.as_slice(), edited.as_slice())
    else {
        panic!("each literal body has a key: {first:?} {edited:?}");
    };
    assert_ne!(one_node, also_node, "the two bodies are two nodes");
    assert_eq!(one, also, "two nodes of one content share a key");
    assert_ne!(
        one_node, edited_node,
        "the arena numbered apart mints the body elsewhere"
    );
    assert_eq!(
        one, edited_one,
        "the key holds over an arena numbered apart"
    );
    assert_ne!(two, edited_two, "the edited literal's key moves");
}

/// #7403: a staged type keys as its base, as a page spells it. A recursive
/// binder's type and the binder's own type are two staged contents, and a
/// key of the sort alone gave both one spelling.
#[test]
fn a_staged_type_keys_as_its_base_7403()
{
    let program = integers(CoreArena::new(), &[]);
    let mut arena = CoreArena::new();
    let unit = arena.value_type_unit();
    let row = arena.value_type_row();
    let stage = gandr_kernel_term::Stage::At(gandr_kernel_term::StageId::from(0_usize));
    let staged_unit = arena.value_type_staged(unit, stage);
    let staged_row = arena.value_type_staged(row, stage);
    let returns_unit = arena.comp_type_returner(unit);
    let thunk = arena.value_type_thunk(returns_unit);
    let returns_staged = arena.comp_type_returner(staged_unit);
    let staged_thunk = arena.value_type_thunk(returns_staged);
    let key = |node| match super::node_key(
        (&arena, program.layout()),
        gandr_core_content::ArenaNode::ValueType(node),
    ) {
        Maybe::Present(key) => key,
        Maybe::Absent(absent) => panic!("each type here has a key: {absent:?}"),
    };
    assert_eq!(
        key(staged_unit),
        key(unit),
        "a staged type keys as its base"
    );
    assert_ne!(
        key(staged_unit),
        key(staged_row),
        "two staged types over two bases key apart"
    );
    assert_eq!(
        key(staged_thunk),
        key(thunk),
        "a former over a staged type keys as the former over its base"
    );
    assert_ne!(
        key(staged_thunk),
        key(staged_unit),
        "a thunk over a staged type keys apart from the staged type"
    );
}

/// #6286: each checkpoint keeps the content key of its item, from a fresh
/// pass and from a resume after an edit alike, so a reader keys the item's
/// outcomes without a second hash, and an edit moves the key of the edited
/// item alone.
#[test]
fn a_checkpoint_keeps_the_content_key_of_its_item_6286()
{
    let kept = |resume: &super::Resume| {
        resume
            .checkpoints()
            .items()
            .iter()
            .map(ItemCheckpoint::key)
            .collect::<vec::Vec<_>>()
    };
    let keyed = |program: &Program| {
        (0 .. program.items().len())
            .map(|index| content_key(program, ItemOrdinal::from(index)))
            .collect::<vec::Vec<_>>()
    };
    let mut first = integers(CoreArena::new(), &[
        (Key("one"), Digits("1")),
        (Key("two"), Digits("2")),
    ]);
    let keys = keyed(&first);
    let checked = super::check_program(&mut first, gandr_core_checker::CheckBudget::DEFAULT)
        .expect("the program checks");
    assert_eq!(kept(&checked), keys, "a fresh pass keeps each item's key");
    let mut edited = integers(noisy(Noise(3)), &[
        (Key("one"), Digits("1")),
        (Key("two"), Digits("20")),
    ]);
    let edited_keys = keyed(&edited);
    let resumed = super::resume(checked, &mut edited).expect("the edit resumes");
    let resumed_keys = kept(&resumed);
    assert_eq!(
        resumed_keys, edited_keys,
        "a resume keeps each edited item's key"
    );
    assert_eq!(
        (
            resumed_keys.first() == keys.first(),
            resumed_keys.get(1) == keys.get(1)
        ),
        (true, false),
        "the edit moves the key of the edited item alone"
    );
    let remade = resumed.checkpoints().items().iter().map(|checkpoint| {
        ItemCheckpoint::new(
            checkpoint.content().clone(),
            checkpoint.footprint().clone(),
            checkpoint.support().to_vec(),
            checkpoint.typing().clone(),
            gandr_core_checker::Entered::AsWritten,
        )
        .key()
    });
    assert!(
        remade.eq(edited_keys),
        "a checkpoint made from its parts, as a decoder makes it, reads the same key"
    );
}
