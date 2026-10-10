//! The differential: incremental equals batch, on named edits and on
//! generated programs and edit chains, with the adoptions each named edit
//! must make.

use alloc::vec;
use alloc::vec::Vec;

use Adoption::Adopted;
use Adoption::Judged;
use gandr_core_checker::CheckBudget;
use gandr_core_checker::Declaration;
use gandr_core_checker::OriginToken;
use gandr_core_checker::signature;
use gandr_core_incremental::Adoption;
use gandr_core_incremental::Answer;
use gandr_core_incremental::Answered;
use gandr_core_incremental::Checkpoints;
use gandr_core_incremental::Item;
use gandr_core_incremental::ItemCheckpoint;
use gandr_core_incremental::ItemCount;
use gandr_core_incremental::ItemKey;
use gandr_core_incremental::Opacity;
use gandr_core_incremental::Program;
use gandr_core_incremental::Reference;
use gandr_core_incremental::TypeContent;
use gandr_core_incremental::Typing;
use gandr_core_incremental::check_program;
use gandr_core_incremental::footprint_of;
use gandr_core_incremental::resume;
use gandr_core_incremental::resume_from;
use gandr_core_term::CoreArena;
use gandr_kernel_term::ConstantIndex;
use proptest::prelude::ProptestConfig;
use proptest::proptest;
use quenchant_shape::shape::Maybe;

use crate::common::Ascription;
use crate::common::Body;
use crate::common::Name;
use crate::common::Natural;
use crate::common::Stmt;
use crate::common::ascribed;
use crate::common::batch;
use crate::common::checked;
use crate::common::def;
use crate::common::gate;
use crate::common::integer;
use crate::common::lower;
use crate::common::read;
use crate::common::step;
use crate::common::text;
use crate::generate::CASES;
use crate::generate::apply;
use crate::generate::program_and_edit;
use crate::generate::program_and_edits;

/// The type content of `String`, read off a program that ascribes it.
///
/// # Specification
/// - ensures: the canonical type table contains exactly the String base type.
/// - panics: the lowering fixture unexpectedly lacks its ascription.
///
/// # Adequacy
/// - hypothesis: L3 — a stale String typing replaces an Integer result and is
///   rejected by the differential; a real type change rechecks its dependent.
/// - witness: `tests::incremental::a_stale_cached_typing_is_caught`
/// - witness: `tests::incremental::type_change_retypes_the_dependent`
#[anodized::spec(
    ensures: |ret| {
        ret.nodes()
            == [gandr_core_incremental::ContentNode::Base(
                gandr_kernel_term::BaseType::String,
            )]
    },
)]
fn string_type() -> TypeContent
{
    let program = lower(&[ascribed(Name("s"), Ascription::Text, Body::Hole)]);
    let Some(Maybe::Present(ty)) = program
        .items()
        .first()
        .map(|item| item.declaration().signature())
    else {
        panic!("the fixture is ascribed");
    };
    TypeContent::of_value_type(&program, ty)
}

/// The base checkpoints of `statements`, replacing every row named `at`.
///
/// # Specification
/// - ensures: retains the default budget and row order; only matching names are
///   passed to the replacement. Duplicate names are all selected.
/// - panics: propagates a replacement panic or a broken fixture-order
///   invariant.
///
/// # Adequacy
/// - hypothesis: L3 — two shadowing names around an unrelated item are both
///   corrupted; the middle checkpoint remains exactly its fresh value. Mutation
///   witnesses separately demonstrate detection of stale typing and footprints.
/// - witness: `tests::incremental::corruption_selects_every_matching_name`
/// - witness: `tests::incremental::a_stale_cached_typing_is_caught`
/// - witness: `tests::incremental::a_suppressed_invalidation_signal_is_caught`
#[anodized::spec(
    ensures: |ret| {
        ret.budget() == CheckBudget::DEFAULT
            && ret.items().len() == statements.len()
            && ret
                .items()
                .iter()
                .zip(statements)
                .all(|(checkpoint, statement)| {
                    statement.name == at.0
                        || match *checkpoint.content().reference() {
                            | Reference::Item { ref key, .. } => {
                                key.as_ref() == statement.name.as_bytes()
                            },
                            | Reference::Unoccupied => false,
                        }
                })
    },
)]
fn corrupted<Replace>(
    statements: &[Stmt],
    at: Name,
    replace: Replace,
) -> Checkpoints
where
    Replace: Fn(ItemCheckpoint) -> ItemCheckpoint,
{
    let base = checked(statements);
    let budget = base.checkpoints().budget();
    let items = base
        .checkpoints()
        .clone()
        .into_items()
        .into_iter()
        .zip(statements)
        .map(|(checkpoint, statement)| {
            if statement.name == at.0 {
                replace(checkpoint)
            }
            else {
                checkpoint
            }
        })
        .collect();
    Checkpoints::new(budget, items)
}

#[test]
fn body_edit_adopts_the_type_stable_dependent()
{
    let step = gate(
        &[
            def(Name("target"), Body::Int(1)),
            def(Name("d"), read(Name("target"))),
        ],
        &[
            def(Name("target"), Body::Int(2)),
            def(Name("d"), read(Name("target"))),
        ],
    );
    assert_eq!(
        step.resumed.adoptions(),
        [Judged, Adopted],
        "the edited definition is judged; its type-stable reader is adopted"
    );
}

#[test]
fn insertion_adopts_untouched_neighbours()
{
    let step = gate(
        &[def(Name("a"), Body::Int(1)), def(Name("c"), Body::Int(3))],
        &[
            def(Name("a"), Body::Int(1)),
            def(Name("b"), Body::Int(2)),
            def(Name("c"), Body::Int(3)),
        ],
    );
    assert_eq!(
        step.resumed.adoptions(),
        [Adopted, Judged, Adopted],
        "only b is fresh"
    );
    assert_eq!(
        step.resumed.adopted_count(),
        ItemCount::from(2_usize),
        "a and c reused"
    );
}

#[test]
fn noop_edit_adopts_everything()
{
    let source = [
        def(Name("a"), Body::Int(1)),
        def(Name("b"), read(Name("a"))),
        def(Name("c"), read(Name("b"))),
    ];
    let step = gate(&source, &source);
    assert_eq!(
        step.resumed.adoptions(),
        [Adopted; 3],
        "an identity edit reuses everything"
    );
    assert_eq!(
        step.resumed.census().judged,
        ItemCount::from(0_usize),
        "and judges nothing"
    );
}

#[test]
fn append_reuses_the_prefix_and_retypes_the_tail()
{
    let step = gate(
        &[
            def(Name("x"), Body::Int(1)),
            def(Name("y"), read(Name("x"))),
        ],
        &[
            def(Name("x"), Body::Int(1)),
            def(Name("y"), read(Name("x"))),
            def(Name("z"), read(Name("y"))),
        ],
    );
    assert_eq!(
        step.resumed.adoptions(),
        [Adopted, Adopted, Judged],
        "the prefix is adopted and only the tail judged"
    );
}

#[test]
fn the_precision_probe_examines_real_adoptions()
{
    let step = gate(
        &[
            def(Name("target"), Body::Int(1)),
            def(Name("reader"), read(Name("target"))),
        ],
        &[
            def(Name("target"), Body::Int(2)),
            def(Name("reader"), read(Name("target"))),
        ],
    );
    assert_eq!(
        step.probed,
        ItemCount::from(1_usize),
        "the probe examined the adopted reader"
    );
    assert_eq!(
        step.resumed.adopted_count(),
        ItemCount::from(1_usize),
        "exactly one adoption"
    );
}

#[test]
fn type_change_retypes_the_dependent()
{
    let step = gate(
        &[
            def(Name("x"), Body::Int(1)),
            def(Name("y"), read(Name("x"))),
        ],
        &[
            def(Name("x"), text(Name("hi"))),
            def(Name("y"), read(Name("x"))),
        ],
    );
    assert_eq!(
        step.resumed.adoptions(),
        [Judged, Judged],
        "y's recorded answer for x no longer holds"
    );
    let produced: Vec<&Typing> = step.resumed.typings().collect();
    assert_eq!(
        produced.get(1),
        Some(&&Typing::Synthesised {
            produced: string_type(),
            conversions: match produced.first() {
                | Some(&&Typing::Synthesised { conversions, .. }) => conversions,
                | other => panic!("x synthesises: {other:?}"),
            },
        }),
        "y now reads a string"
    );
}

#[test]
fn downstream_error_surfaces()
{
    let step = gate(
        &[
            def(Name("x"), Body::Int(1)),
            ascribed(Name("y"), Ascription::Integer, read(Name("x"))),
        ],
        &[
            def(Name("x"), text(Name("hi"))),
            ascribed(Name("y"), Ascription::Integer, read(Name("x"))),
        ],
    );
    assert_eq!(
        step.resumed.adoptions().get(1),
        Some(&Judged),
        "y is judged against the new x"
    );
    assert!(
        matches!(
            step.resumed.typings().nth(1),
            Some(&Typing::Refused(
                gandr_core_incremental::Refusal::TypeMismatch { .. }
            ))
        ),
        "the ascription fails once x is a string"
    );
}

#[test]
fn ascription_change_alone_invalidates_the_item()
{
    let step = gate(
        &[def(Name("a"), Body::Int(1)), def(Name("b"), Body::Int(2))],
        &[
            ascribed(Name("a"), Ascription::Text, Body::Int(1)),
            def(Name("b"), Body::Int(2)),
        ],
    );
    assert_eq!(
        step.resumed.adoptions(),
        [Judged, Adopted],
        "the ascription is content"
    );
    assert!(
        matches!(
            step.resumed.typings().next(),
            Some(&Typing::Refused(
                gandr_core_incremental::Refusal::TypeMismatch { .. }
            ))
        ),
        "an integer does not satisfy String"
    );
}

#[test]
fn satisfied_ascription_types_and_keeps_dependents_adoptable()
{
    let step = gate(
        &[
            ascribed(Name("a"), Ascription::Integer, Body::Int(1)),
            def(Name("b"), read(Name("a"))),
        ],
        &[
            ascribed(Name("a"), Ascription::Integer, Body::Int(7)),
            def(Name("b"), read(Name("a"))),
        ],
    );
    assert_eq!(
        step.resumed.adoptions(),
        [Judged, Adopted],
        "a keeps its type under the ascription, so b stays adoptable"
    );
}

#[test]
fn deletion_matches_from_scratch()
{
    let step = gate(
        &[
            def(Name("a"), Body::Int(1)),
            def(Name("b"), Body::Int(2)),
            def(Name("c"), Body::Int(3)),
        ],
        &[def(Name("a"), Body::Int(1)), def(Name("c"), Body::Int(3))],
    );
    assert_eq!(
        step.resumed.adoptions(),
        [Adopted, Adopted],
        "both survivors reused"
    );
    assert_eq!(
        step.resumed.census().splice.removed,
        ItemCount::from(1_usize),
        "b's handle left the order"
    );
}

#[test]
fn rename_matches_from_scratch()
{
    let step = gate(
        &[
            def(Name("foo"), Body::Int(1)),
            def(Name("keep"), Body::Int(9)),
        ],
        &[
            def(Name("bar"), Body::Int(1)),
            def(Name("keep"), Body::Int(9)),
        ],
    );
    assert_eq!(
        step.resumed.adoptions(),
        [Judged, Adopted],
        "keep is adopted across the rename"
    );
}

#[test]
fn coordinated_rename_rebinds_every_reader()
{
    let step = gate(
        &[
            def(Name("old"), Body::Int(1)),
            def(Name("reader"), read(Name("old"))),
            def(Name("bystander"), Body::Int(9)),
        ],
        &[
            def(Name("new"), Body::Int(1)),
            def(Name("reader"), read(Name("new"))),
            def(Name("bystander"), Body::Int(9)),
        ],
    );
    assert_eq!(
        step.resumed.adoptions(),
        [Judged, Judged, Adopted],
        "the renamed definition and its reader are fresh; the bystander is reused"
    );
    assert!(
        matches!(
            step.resumed.typings().nth(1),
            Some(&Typing::Synthesised { .. })
        ),
        "the reader binds the new name rather than dangling"
    );
}

#[test]
fn uncoordinated_rename_leaves_a_dangling_reader()
{
    let step = gate(
        &[
            def(Name("old"), Body::Int(1)),
            ascribed(Name("reader"), Ascription::Integer, read(Name("old"))),
        ],
        &[
            def(Name("new"), Body::Int(1)),
            ascribed(Name("reader"), Ascription::Integer, read(Name("old"))),
        ],
    );
    assert_eq!(
        step.resumed.adoptions().get(1),
        Some(&Judged),
        "the reader's name left scope"
    );
    assert!(
        matches!(
            step.resumed.typings().nth(1),
            Some(&Typing::Refused(
                gandr_core_incremental::Refusal::UnknownConstant {
                    constant: Reference::Unoccupied,
                    ..
                }
            ))
        ),
        "and is refused as batch refuses it"
    );
}

#[test]
fn independent_swap_matches_from_scratch()
{
    let step = gate(
        &[
            def(Name("a"), Body::Int(1)),
            def(Name("b"), text(Name("s"))),
            def(Name("c"), Body::Int(3)),
        ],
        &[
            def(Name("c"), Body::Int(3)),
            def(Name("b"), text(Name("s"))),
            def(Name("a"), Body::Int(1)),
        ],
    );
    assert_eq!(
        step.resumed.adoptions(),
        [Adopted; 3],
        "content, not position, is identity"
    );
}

#[test]
fn swap_past_a_reader_matches_from_scratch()
{
    let step = gate(
        &[
            def(Name("x"), Body::Int(1)),
            ascribed(Name("y"), Ascription::Integer, read(Name("x"))),
        ],
        &[
            ascribed(Name("y"), Ascription::Integer, read(Name("x"))),
            def(Name("x"), Body::Int(1)),
        ],
    );
    assert!(
        matches!(
            step.resumed.typings().next(),
            Some(&Typing::Refused(
                gandr_core_incremental::Refusal::UnknownConstant { .. }
            ))
        ),
        "y now precedes x, so its name is unbound"
    );
    assert_eq!(
        step.resumed.adoptions().get(1),
        Some(&Adopted),
        "x itself is reused"
    );
}

#[test]
fn a_stale_cached_typing_is_caught()
{
    let source = [def(Name("a"), Body::Int(1)), def(Name("b"), Body::Int(2))];
    assert_eq!(
        gate(&source, &source).resumed.adopted_count(),
        ItemCount::from(2_usize),
        "the honest identity edit adopts both"
    );
    let stale = corrupted(&source, Name("a"), |checkpoint| {
        let conversions = match *checkpoint.typing() {
            | Typing::Synthesised { conversions, .. } => conversions,
            | ref other => panic!("a synthesises: {other:?}"),
        };
        checkpoint.with_typing(Typing::Synthesised {
            produced: string_type(),
            conversions,
        })
    });
    let mut program = lower(&source);
    let expected = batch(&program);
    let resumed = resume_from(&stale, &mut program).expect("the order builds");
    assert_eq!(
        resumed.adoptions().first(),
        Some(&Adopted),
        "the stale checkpoint is still adopted, which is what makes it dangerous"
    );
    assert_ne!(
        resumed.typings().cloned().collect::<Vec<Typing>>(),
        expected,
        "the differential catches the stale typing"
    );
    assert!(
        matches!(
            step(resumed, &mut lower(&source)),
            Err(proptest::test_runner::TestCaseError::Fail(_)),
        ),
        "the differential step must fail, not discard a stale-typing case"
    );
}

#[test]
fn a_suppressed_invalidation_signal_is_caught()
{
    let base = [
        def(Name("x"), Body::Int(1)),
        def(Name("y"), read(Name("x"))),
    ];
    let edited = [
        def(Name("x"), text(Name("hi"))),
        def(Name("y"), read(Name("x"))),
    ];
    assert_eq!(
        gate(&base, &edited).resumed.adopted_count(),
        ItemCount::from(0_usize),
        "with honest support the changed answer re-judges both"
    );
    // y's support claims x already answered String, so the changed answer
    // matches it and nothing signals the change.
    let suppressed = corrupted(&base, Name("y"), |checkpoint| {
        let support = checkpoint
            .support()
            .iter()
            .map(|answered| {
                Answered::new(answered.reference().clone(), Answer::Typed(string_type()))
            })
            .collect();
        checkpoint.with_support(support)
    });
    let mut program = lower(&edited);
    let expected = batch(&program);
    let resumed = resume_from(&suppressed, &mut program).expect("the order builds");
    assert_eq!(
        resumed.adoptions().get(1),
        Some(&Adopted),
        "the suppressed signal lets y adopt across a changed answer"
    );
    assert_ne!(
        resumed.typings().cloned().collect::<Vec<Typing>>(),
        expected,
        "the differential catches the over-adoption"
    );
}

#[test]
fn a_stored_footprint_is_not_an_adoption_input()
{
    let program_for = |value| {
        vec![
            def(Name("one"), Body::Int(value)),
            ascribed(
                Name("r"),
                Ascription::CodeOf(String::from("one")),
                Body::Int(7),
            ),
            def(Name("bystander"), Body::Int(9)),
        ]
    };
    let base = program_for(1);
    // r's stored footprint is replaced by the bystander's, which reads nothing.
    let empty = checked(&base)
        .checkpoints()
        .items()
        .get(2)
        .map(|checkpoint| checkpoint.footprint().clone())
        .expect("three items");
    let narrowed = corrupted(&base, Name("r"), |checkpoint| {
        checkpoint.with_footprint(empty.clone())
    });
    let mut program = lower(&program_for(2));
    let expected = batch(&program);
    let resumed = resume_from(&narrowed, &mut program).expect("the order builds");
    assert_eq!(
        resumed.adoptions(),
        [Judged, Judged, Adopted],
        "r reads a changed value in a type position, whatever its stored footprint says"
    );
    assert_eq!(
        resumed.typings().cloned().collect::<Vec<Typing>>(),
        expected,
        "and a narrowed stored footprint changes no answer"
    );
}

#[test]
fn an_ascription_endpoint_is_a_read()
{
    let program_for = |value| {
        vec![
            def(Name("one"), Body::Int(value)),
            ascribed(
                Name("r"),
                Ascription::CodeOf(String::from("one")),
                Body::Int(7),
            ),
            def(Name("bystander"), Body::Int(9)),
        ]
    };
    let reader = footprint_of(
        checked(&program_for(1))
            .checkpoints()
            .items()
            .get(1)
            .expect("three items")
            .content(),
    );
    let one = Reference::Item {
        key: ItemKey::from("one"),
        occurrence: gandr_core_incremental::Occurrence::from(0_usize),
    };
    assert_eq!(
        reader.reads().collect::<Vec<_>>(),
        [&one],
        "r's term mentions nothing; its type mentions one"
    );
    assert_eq!(
        reader.type_reads().collect::<Vec<_>>(),
        [&one],
        "and that mention is a type position"
    );
    assert_eq!(
        gate(&program_for(1), &program_for(1)).resumed.adoptions(),
        [Adopted; 3],
        "unedited, r is adopted"
    );
    assert_eq!(
        gate(&program_for(1), &program_for(2)).resumed.adoptions(),
        [Judged, Judged, Adopted],
        "a value change to one reaches r through its type, and not the bystander"
    );
}

#[test]
fn a_type_stable_body_edit_reaches_a_type_position()
{
    let program_for = |value| {
        vec![
            def(Name("one"), Body::Int(value)),
            ascribed(
                Name("r"),
                Ascription::CodeOf(String::from("one")),
                read(Name("one")),
            ),
            def(Name("bystander"), Body::Int(9)),
        ]
    };
    let base = checked(&program_for(1));
    let reader = base.checkpoints().items().get(1).expect("three items");
    assert_eq!(
        reader.footprint().opacity(),
        Opacity::Transparent,
        "the case means something only if r is not conservatively opaque"
    );
    assert_eq!(
        reader.footprint().reads().count(),
        1_usize,
        "r's term reads one"
    );
    let step = gate(&program_for(1), &program_for(2));
    assert_eq!(
        step.resumed.typings().next(),
        base.typings().next(),
        "one's type stands still; only its value moved"
    );
    assert_eq!(
        step.resumed.adoptions(),
        [Judged, Judged, Adopted],
        "the value change reaches r's type position"
    );
}

#[test]
fn a_changed_value_reaches_through_an_untouched_definition()
{
    let program_for = |value| {
        vec![
            def(Name("c"), Body::Int(value)),
            def(Name("b"), read(Name("c"))),
            ascribed(
                Name("x"),
                Ascription::CodeOf(String::from("b")),
                Body::Int(7),
            ),
            def(Name("bystander"), Body::Int(9)),
        ]
    };
    let intermediate = checked(&program_for(1));
    let b = intermediate
        .checkpoints()
        .items()
        .get(1)
        .expect("four items");
    assert_eq!(
        b.footprint().reads().collect::<Vec<_>>(),
        [&Reference::Item {
            key: ItemKey::from("c"),
            occurrence: gandr_core_incremental::Occurrence::from(0_usize),
        }],
        "b's own term reads c and is untouched by the edit"
    );
    let step = gate(&program_for(1), &program_for(2));
    assert_eq!(
        step.resumed.adoptions(),
        [Judged, Adopted, Judged, Adopted],
        "b is adopted on its type, x is judged through the closure, the bystander is reused"
    );
    let census = step.resumed.census();
    assert_eq!(census.seeds, ItemCount::from(1_usize), "only c is seeded");
    assert_eq!(
        census.value_changed,
        ItemCount::from(3_usize),
        "b and x join through the closure"
    );
}

#[test]
fn an_opaque_footprint_is_never_adopted()
{
    // An id past anything the program's arena holds.
    let mut foreign = CoreArena::new();
    for _ in 0_usize .. 64_usize {
        let _unit = foreign.value_unit();
    }
    let foreign = foreign.value_unit();
    let program_for = |fresh: Name| {
        let mut arena = CoreArena::new();
        let mut items = Vec::new();
        let mut push = |key: &str, body| {
            let position = items.len();
            items.push(Item::new(
                ItemKey::from(key),
                Declaration::new(
                    ConstantIndex::from(position),
                    Maybe::Absent(signature::Absent::Unsigned),
                    Maybe::Present(body),
                    OriginToken::from(position),
                ),
            ));
        };
        if !fresh.0.is_empty() {
            push(fresh.0, arena.value_literal(integer(Natural(0))));
        }
        push("plain", arena.value_literal(integer(Natural(1))));
        let literal = arena.value_literal(integer(Natural(1)));
        push("opaque", arena.value_pair(literal, foreign));
        Program::new(arena, items).expect("positions ascend")
    };
    let mut base = program_for(Name(""));
    let opaque = base.items().len() - 1;
    let base = check_program(&mut base, CheckBudget::DEFAULT).expect("the order builds");
    assert_eq!(
        base.checkpoints()
            .items()
            .get(opaque)
            .map(|checkpoint| checkpoint.footprint().opacity()),
        Some(Opacity::Opaque),
        "the foreign id makes the item opaque"
    );
    let mut edited = program_for(Name("fresh"));
    let expected = batch(&edited);
    let resumed = resume(base, &mut edited).expect("the order builds");
    assert_eq!(
        resumed.typings().cloned().collect::<Vec<Typing>>(),
        expected,
        "incremental equals batch"
    );
    assert_eq!(
        resumed.adoptions(),
        [Judged, Adopted, Judged],
        "the transparent item is reused; the opaque one never is"
    );
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(CASES))]

    /// Over a generated program and one edit, the resume equals batch, every
    /// adoption passes the probe, and the checkpoints survive persistence.
    #[test]
    fn incremental_equals_from_scratch((statements, edit) in program_and_edit()) {
        let edited = apply(&statements, &edit);
        let _step = step(checked(&statements), &mut lower(&edited))?;
    }

    /// Over a chain of edits, each step resumes from the previous step's
    /// result, so drift that accumulates across resumes is caught where it
    /// first matters.
    #[test]
    fn edit_sequences_preserve_zero_drift((statements, edits) in program_and_edits()) {
        let mut current = statements;
        let mut resumed = checked(&current);
        for edit in &edits {
            current = apply(&current, edit);
            resumed = step(resumed, &mut lower(&current))?.resumed;
        }
    }
}

#[test]
fn corruption_selects_every_matching_name()
{
    let source = [
        def(Name("x"), Body::Int(1)),
        def(Name("middle"), Body::Int(2)),
        def(Name("x"), Body::Int(3)),
    ];
    let fresh = checked(&source);
    let corrupted = corrupted(&source, Name("x"), |checkpoint| {
        checkpoint.with_typing(Typing::Owed)
    });
    let expected = fresh
        .checkpoints()
        .items()
        .iter()
        .cloned()
        .enumerate()
        .map(|(index, checkpoint)| {
            if index == 1 {
                checkpoint
            }
            else {
                checkpoint.with_typing(Typing::Owed)
            }
        })
        .collect::<Vec<_>>();
    assert_eq!(corrupted, Checkpoints::new(CheckBudget::DEFAULT, expected));
}
