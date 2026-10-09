//! Witnesses that the four defects of the prior implementation are absent:
//! value-mediated over-adoption out of the generator's reach, a hang on
//! shadowing under a type-position read, rechecking that grows faster than
//! the program, and a failed store that changes the store.

use alloc::collections::BTreeMap;
use alloc::format;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;

use gandr_core_checker::CheckBudget;
use gandr_core_checker::Declaration;
use gandr_core_checker::OriginToken;
use gandr_core_checker::signature;
use gandr_core_incremental::BackendArtifact;
use gandr_core_incremental::CheckpointStore as _;
use gandr_core_incremental::CheckpointStoreError;
use gandr_core_incremental::FileCheckpointStore;
use gandr_core_incremental::Item;
use gandr_core_incremental::ItemCount;
use gandr_core_incremental::ItemKey;
use gandr_core_incremental::MemoryCheckpointStore;
use gandr_core_incremental::Program;
use gandr_core_incremental::RecordCount;
use gandr_core_incremental::ResumeCensus;
use gandr_core_incremental::Sort;
use gandr_core_incremental::SpliceCensus;
use gandr_core_incremental::Typing;
use gandr_core_incremental::UnsupportedPersistence;
use gandr_core_incremental::address_of;
use gandr_core_incremental::check_program;
use gandr_core_term::CoreArena;
use gandr_kernel_term::ConstantIndex;
use proptest::strategy::Strategy as _;
use proptest::strategy::ValueTree as _;
use proptest::test_runner::TestRunner;
use quenchant_shape::shape::Maybe;

use crate::common::Ascription;
use crate::common::Body;
use crate::common::Label;
use crate::common::Name;
use crate::common::Natural;
use crate::common::Scratch;
use crate::common::Stmt;
use crate::common::ascribed;
use crate::common::checked;
use crate::common::def;
use crate::common::gate;
use crate::common::integer;
use crate::common::lower;
use crate::common::read;
use crate::generate::CASES;
use crate::generate::Edit;
use crate::generate::Rank;
use crate::generate::Revalued;
use crate::generate::apply;
use crate::generate::program_and_edit;
use crate::generate::revalue;

/// Whether `edit` changes an integer body of `statements` to another
/// integer: a value-only edit.
///
/// # Specification
/// trivial.
fn value_only(
    statements: &[Stmt],
    edit: &Edit,
) -> Reached
{
    let mut statements = statements.to_vec();
    match *edit {
        | Edit::Revalue(rank, value)
            if revalue(&mut statements, Rank(rank), Natural(value)) == Revalued::Changed =>
        {
            Reached::Yes
        },
        | _ => Reached::No,
    }
}

/// Whether a generated case reached the shape under census.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Reached
{
    /// It did not.
    No,
    /// It did.
    Yes,
}

#[test]
fn the_generator_reaches_value_only_edits_under_type_position_reads()
{
    let mut runner = TestRunner::deterministic();
    let strategy = program_and_edit();
    let mut census: BTreeMap<(Reached, Reached), usize> = BTreeMap::new();
    for _ in 0_u32 .. CASES {
        let (statements, edit) = strategy
            .new_tree(&mut runner)
            .expect("the strategy generates")
            .current();
        let edited = apply(&statements, &edit);
        let step = gate(&statements, &edited);
        let guarded = if usize::from(step.resumed.census().value_reads) > 0_usize {
            Reached::Yes
        }
        else {
            Reached::No
        };
        let entry = census
            .entry((value_only(&statements, &edit), guarded))
            .or_default();
        *entry = entry.saturating_add(1);
    }
    let count = |key| census.get(&key).copied().unwrap_or_default();
    let value_only_edits =
        count((Reached::Yes, Reached::No)).saturating_add(count((Reached::Yes, Reached::Yes)));
    let guarded =
        count((Reached::No, Reached::Yes)).saturating_add(count((Reached::Yes, Reached::Yes)));
    let both = count((Reached::Yes, Reached::Yes));
    // The deterministic runner gives 92 value-only edits, 35 cases where the
    // guard fired and 19 where both met; the floors sit at about half, so a
    // generator change that loses the class fails here rather than passing
    // the property vacuously.
    assert!(
        value_only_edits >= 45_usize && guarded >= 17_usize && both >= 9_usize,
        "of {CASES} deterministic cases: {value_only_edits} value-only edits, {guarded} guards fired, {both} both"
    );
}

#[test]
fn a_shadowing_program_under_a_type_position_read_checks_and_terminates()
{
    // d0 = 1; d1 = d0; d0 = d1; r : El 0 d0 = 7 — the shadowing that made the
    // prior implementation's definitional environment cyclic.
    let program_for = |value| {
        vec![
            def(Name("d0"), Body::Int(value)),
            def(Name("d1"), read(Name("d0"))),
            def(Name("d0"), read(Name("d1"))),
            ascribed(
                Name("r"),
                Ascription::CodeOf(String::from("d0")),
                Body::Int(7),
            ),
        ]
    };
    let base = checked(&program_for(1));
    assert!(
        base.typings()
            .take(3)
            .all(|typing| matches!(*typing, Typing::Synthesised { .. })),
        "each definition reads the one before it, so every one synthesises"
    );
    let step = gate(&program_for(1), &program_for(2));
    assert_eq!(
        step.resumed.census().value_changed,
        ItemCount::from(4_usize),
        "the value change closes over the shadowing chain and the type-position read, and stops"
    );
}

/// The chain `d0 = head; d1 = d0; …` of `length` definitions.
///
/// # Specification
/// trivial.
fn chain(
    length: ItemCount,
    head: Body,
) -> Vec<Stmt>
{
    let mut statements = vec![Stmt {
        name: String::from("d0"),
        ascription: None,
        body: head,
    }];
    for index in 1 .. usize::from(length) {
        statements.push(Stmt {
            name: format!("d{index}"),
            ascription: None,
            body: Body::Ref(format!("d{}", index.saturating_sub(1))),
        });
    }
    statements
}

#[test]
fn items_visited_for_a_head_edit_grow_linearly()
{
    for length in [250_usize, 500_usize, 1000_usize, 2000_usize] {
        let all = ItemCount::from(length);
        let rest = ItemCount::from(length.saturating_sub(1));
        let none = ItemCount::from(0_usize);
        let one = ItemCount::from(1_usize);
        let untouched = SpliceCensus {
            kept: all,
            inserted: none,
            removed: none,
        };
        let base = chain(all, Body::Int(1));

        let value_only = gate(&base, &chain(all, Body::Int(2))).resumed.census();
        assert_eq!(
            value_only,
            ResumeCensus {
                items: all,
                recalled: all,
                adopted: rest,
                judged: one,
                minted: rest,
                outdated: none,
                value_reads: none,
                seeds: one,
                closure_edges: rest,
                value_changed: all,
                splice: untouched,
            },
            "a value-only head edit of a chain of {length}: one judgement, one crossing per edge"
        );

        let type_changing = gate(&base, &chain(all, Body::Str(String::from("s"))))
            .resumed
            .census();
        assert_eq!(
            type_changing,
            ResumeCensus {
                items: all,
                recalled: all,
                adopted: none,
                judged: all,
                minted: rest,
                outdated: rest,
                value_reads: none,
                seeds: one,
                closure_edges: rest,
                value_changed: all,
                splice: untouched,
            },
            "a type-changing head edit of a chain of {length}: each item judged once"
        );
    }
}

/// A one-item program whose body holds an id no arena of it resolves.
///
/// # Specification
/// trivial.
fn opaque_program() -> Program
{
    let mut foreign = CoreArena::new();
    for _ in 0_usize .. 64_usize {
        let _unit = foreign.value_unit();
    }
    let foreign = foreign.value_unit();
    let mut arena = CoreArena::new();
    let literal = arena.value_literal(integer(Natural(1)));
    let pair = arena.value_pair(literal, foreign);
    Program::new(arena, vec![Item::new(
        ItemKey::from("opaque"),
        Declaration::new(
            ConstantIndex::from(0_usize),
            Maybe::Absent(signature::Absent::Unsigned),
            Maybe::Present(pair),
            OriginToken::from(0_usize),
        ),
    )])
    .expect("one item ascends")
}

#[test]
fn a_failed_store_leaves_the_store_as_it_was()
{
    let backend = BackendArtifact::from(b"core-checker".as_slice());
    let mut good_program = lower(&[def(Name("a"), Body::Int(1))]);
    let address = address_of(&good_program).expect("resolved");
    let good = check_program(&mut good_program, CheckBudget::DEFAULT)
        .expect("the order builds")
        .checkpoints()
        .clone();
    let bad = check_program(&mut opaque_program(), CheckBudget::DEFAULT)
        .expect("the order builds")
        .checkpoints()
        .clone();
    let refused = Err(CheckpointStoreError::UnsupportedPersistence(
        UnsupportedPersistence::Dangling(Sort::Value),
    ));

    let mut memory = MemoryCheckpointStore::default();
    memory.store(address, backend, &good).expect("stored");
    let before = memory.clone();
    assert_eq!(
        memory.store(address, backend, &bad),
        refused,
        "the memory store refuses"
    );
    assert_eq!(memory, before, "and holds what it held");
    assert_eq!(
        memory.record_count(),
        RecordCount::from(1_usize),
        "one record"
    );
    assert_eq!(
        memory.load(address, backend),
        Ok(Maybe::Present(good.clone())),
        "the good one"
    );

    let scratch = Scratch::new(Label("failed-store"));
    let mut file = FileCheckpointStore::open(scratch.path()).expect("open");
    file.store(address, backend, &good).expect("stored");
    let before = scratch.snapshot();
    assert_eq!(
        file.store(address, backend, &bad),
        refused,
        "the file store refuses"
    );
    assert_eq!(
        scratch.snapshot(),
        before,
        "and the directory is byte-identical"
    );
    assert_eq!(
        file.load(address, backend),
        Ok(Maybe::Present(good)),
        "the good record loads"
    );
}
