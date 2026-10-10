//! Witnesses for generator reachability, termination under shadowing,
//! linear rechecking work, and failure-atomic persistence.

use alloc::collections::BTreeMap;
use alloc::format;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;
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
/// - ensures: answers Yes exactly when the modular integer selection changes
///   its value; other edits and absent integer bodies answer No.
///
/// # Adequacy
/// - hypothesis: L3 — the deterministic census requires actual value-only
///   mutations, including cases under a type-position read; direct mutation
///   boundaries distinguish changed, equal and absent integer selections.
/// - witness: `tests::defects::the_generator_reaches_value_only_edits_under_type_position_reads`
/// - witness: `tests::generate::revalue_preserves_metadata_and_classifies_exactly`
#[spec(
    ensures: |ret| {
        (ret == Reached::Yes)
            == match *edit {
                | Edit::Revalue(rank, value) => {
                    let count = statements
                        .iter()
                        .filter(|statement| matches!(statement.body, Body::Int(_)))
                        .count();
                    rank.checked_rem(count)
                        .and_then(|rank| {
                            statements
                                .iter()
                                .filter_map(|statement| match statement.body {
                                    | Body::Int(old) => Some(old),
                                    | _ => None,
                                })
                                .nth(rank)
                        })
                        .is_some_and(|old| old != value)
                },
                | _ => false,
            }
    },
)]
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
/// - ensures: produces exactly length unsigned definitions, including none for
///   zero; the first holds head and each later body reads its predecessor.
///
/// # Adequacy
/// - hypothesis: L3 — zero and singleton lengths pin the empty boundary and
///   head payload. Chains of 250 through 2000 definitions exercise both value
///   and type changes; their exact work census is distinct from this structural
///   predicate, which captures only the head variant rather than cloning it.
/// - witness: `tests::defects::chain_respects_zero_and_singleton_lengths`
/// - witness: `tests::defects::items_visited_for_a_head_edit_grow_linearly`
#[spec(
    captures: [head_kind = core::mem::discriminant(&head)],
    ensures: |ret| {
        ret.len() == usize::from(length)
            && ret.iter().all(|statement| statement.ascription.is_none())
            && ret.first().is_none_or(|first| {
                first.name == "d0" && core::mem::discriminant(&first.body) == head_kind
            })
            && ret.windows(2).all(|pair| match *pair {
                | [ref earlier, ref later] => match later.body {
                    | Body::Ref(ref name) => name == &earlier.name,
                    | _ => false,
                },
                | _ => false,
            })
    },
)]
fn chain(
    length: ItemCount,
    head: Body,
) -> Vec<Stmt>
{
    let mut statements = Vec::with_capacity(usize::from(length));
    if usize::from(length) != 0 {
        statements.push(Stmt {
            name: String::from("d0"),
            ascription: None,
            body: head,
        });
    }
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
/// - ensures: one unsigned item at position zero has a pair body whose first
///   child resolves and whose second child is deliberately unresolved.
/// - provides: a malformed input for refusal and failure-atomicity witnesses,
///   not evidence that the arena constructor's valid-child domain is met.
///
/// # Adequacy
/// - hypothesis: L3 — both stores reject the resulting dangling Value content
///   without changing the prior record or file bytes. The predicate
///   independently observes the one resolving and one missing child, without
///   running the codec.
/// - witness: `tests::defects::a_failed_store_leaves_the_store_as_it_was`
#[spec(
    ensures: |ret| {
        ret.items().len() == 1
            && ret.items().first().is_some_and(|item| {
                let declaration = item.declaration();
                item.key().as_ref() == b"opaque"
                    && usize::from(declaration.constant()) == 0
                    && usize::from(declaration.origin()) == 0
                    && declaration.signature() == Maybe::Absent(signature::Absent::Unsigned)
                    && match declaration.body() {
                        | Maybe::Present(root) => match ret.arena().value(root) {
                            | Some(&gandr_core_term::Value::Pair(first, second)) => {
                                ret.arena().value(first).is_some()
                                    && ret.arena().value(second).is_none()
                            },
                            | _ => false,
                        },
                        | Maybe::Absent(_) => false,
                    }
            })
    },
)]
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

#[test]
fn chain_respects_zero_and_singleton_lengths()
{
    assert_eq!(chain(ItemCount::from(0_usize), Body::Int(7)), []);
    assert_eq!(chain(ItemCount::from(1_usize), Body::Int(7)), [Stmt {
        name: String::from("d0"),
        ascription: None,
        body: Body::Int(7)
    },]);
}
