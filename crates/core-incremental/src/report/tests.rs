use alloc::collections::BTreeSet;
use alloc::vec;
use alloc::vec::Vec;

use gandr_core_checker::body;
use gandr_core_term::CoreArena;
use gandr_core_term::Sort;
use gandr_core_term::Zone;
use gandr_core_term::support::Thinning;
use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::GroundSort;
use quenchant_shape::shape::Maybe;

use crate::boundary::ItemOrdinal;
use crate::boundary::NodeIndex;
use crate::boundary::OutsideIndex;
use crate::content::TablePlace;
use crate::fixture::Digits;
use crate::fixture::Position;
use crate::fixture::checked;
use crate::fixture::declaration;
use crate::fixture::integer;
use crate::region::Item;
use crate::region::ItemKey;
use crate::region::Program;

/// A body that runs two nested calls of the identity is elaborated, and a
/// declaration whose declared type decodes an owed hole is suspended. Each
/// keeps its report in its checkpoint, the set reads back from its bytes, and
/// each report seats in the program's arena as the parts that give it again:
/// the two decisions and the one bind of the elaboration, and the suspension
/// blocked on the hole.
#[test]
fn a_report_read_back_from_bytes_seats_as_the_parts_that_give_it()
{
    // def id      : U (Integer -> F Integer) = thunk λ. return x ;
    // def twice   : U (Integer -> F Integer) = thunk λ. return {id {id x}} ;
    // def hole    : Type = ? ;
    // def waiting : El hole = 0 ;
    let mut arena = CoreArena::new();
    let integer_type = arena.value_type_base(BaseType::Integer);
    let returns = arena.comp_type_returner(integer_type);
    let arrow = arena.comp_type_arrow(integer_type, returns);
    let function = arena.value_type_thunk(arrow);
    let argument = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let returned = arena.computation_return(argument);
    let lambda = arena.computation_lambda(returned);
    let identity = arena.value_thunk(lambda);
    let call = |arena: &mut CoreArena, argument| {
        let callee = arena.value_constant(ConstantIndex::from(0_usize));
        let forced = arena.computation_force(callee);
        arena.computation_application(forced, argument)
    };
    let inner = call(&mut arena, argument);
    let inner = arena.value_nested(inner);
    let outer = call(&mut arena, inner);
    let outer = arena.value_nested(outer);
    let returned = arena.computation_return(outer);
    let lambda = arena.computation_lambda(returned);
    let twice = arena.value_thunk(lambda);
    let universe = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let hole = arena.value_constant(ConstantIndex::from(2_usize));
    let decoded = arena.value_type_element(hole, Level::zero());
    let zero = arena.value_literal(integer(Digits("0")));
    let item = |key: &str, position, (signature, body)| {
        Item::new(
            ItemKey::from(key),
            declaration(Position(position), signature, body),
        )
    };
    let mut program = Program::new(arena, vec![
        item(
            "id",
            0,
            (Maybe::Present(function), Maybe::Present(identity)),
        ),
        item(
            "twice",
            1,
            (Maybe::Present(function), Maybe::Present(twice)),
        ),
        item(
            "hole",
            2,
            (Maybe::Present(universe), Maybe::Absent(body::Absent::Hole)),
        ),
        item(
            "waiting",
            3,
            (Maybe::Present(decoded), Maybe::Present(zero)),
        ),
    ])
    .expect("positions ascend");
    let checkpoints = checked(&mut program);
    let bytes = crate::encode_checkpoints(&checkpoints).expect("the set persists");
    let read = crate::decode_checkpoints(&bytes).expect("the set reads back");
    let reported: Vec<_> = read
        .items()
        .iter()
        .enumerate()
        .filter_map(|(ordinal, checkpoint)| match checkpoint.report() {
            Maybe::Present(report) => Some((ItemOrdinal::from(ordinal), checkpoint, report)),
            Maybe::Absent(_) => None,
        })
        .collect();
    let [
        (elaborated_at, elaborated, elaboration_kept),
        (suspended_at, suspended, suspension_kept),
    ] = reported[..]
    else {
        panic!("the elaborated and the suspended item keep a report: {reported:?}");
    };
    assert_eq!(
        (usize::from(elaborated_at), usize::from(suspended_at)),
        (1, 3),
        "no other item keeps a report"
    );
    let mut arena = program.arena().clone();
    let Maybe::Present(seated) = elaborated.reported(&mut arena, (&program, elaborated_at))
    else {
        panic!("the elaboration seats");
    };
    assert_eq!(
        seated.content(&arena, (&program, elaborated_at)),
        Maybe::Present(elaboration_kept.clone()),
        "the seated elaboration gives the report kept"
    );
    let Maybe::Present(elaboration) = seated.elaboration()
    else {
        panic!("the seat builds the elaboration again");
    };
    assert_eq!(
        (elaboration.decisions().len(), elaboration.binds().len()),
        (2, 1),
        "both nested calls are decided, and the inner one mints a bind"
    );
    let mut arena = program.arena().clone();
    let Maybe::Present(seated) = suspended.reported(&mut arena, (&program, suspended_at))
    else {
        panic!("the suspension seats");
    };
    assert_eq!(
        seated.content(&arena, (&program, suspended_at)),
        Maybe::Present(suspension_kept.clone()),
        "the seated suspension gives the report kept"
    );
    let Maybe::Present(suspension) = seated.suspension()
    else {
        panic!("the seat builds the suspension again");
    };
    assert_eq!(
        suspension.blockers(),
        &BTreeSet::from([ConstantIndex::from(2_usize)]),
        "the suspension is blocked on the hole"
    );
}

/// Roots that share a place keep that place once, in the order of its first
/// root, and each root takes the index of its place. Roots at distinct places
/// keep their own indices.
#[test]
fn roots_that_share_a_place_keep_it_once()
{
    let place = |node: usize| TablePlace {
        node: NodeIndex::from(node),
        support: Thinning::empty(),
    };
    let index = OutsideIndex::from;
    assert_eq!(
        super::merged(vec![place(4), place(7), place(4), place(9)]),
        (
            vec![place(4), place(7), place(9)],
            Some(vec![index(0), index(1), index(0), index(2)])
        ),
        "the second root at the first place takes its index"
    );
    assert_eq!(
        super::merged(vec![place(4), place(7)]),
        (vec![place(4), place(7)], None),
        "distinct places keep their indices"
    );
}

/// The program `waiting`, whose declared type decodes an owed hole, followed
/// by `reader` of that type, whose body reads `waiting`.
///
/// # Specification
/// trivial.
fn waiting_and(reader: ItemKey) -> Program
{
    // def hole    : Type = ? ;
    // def waiting : El hole = 0 ;
    // def reader  : El hole = waiting ;
    let mut arena = CoreArena::new();
    let universe = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let hole = arena.value_constant(ConstantIndex::from(0_usize));
    let decoded = arena.value_type_element(hole, Level::zero());
    let zero = arena.value_literal(integer(Digits("0")));
    let waiting = arena.value_constant(ConstantIndex::from(1_usize));
    let item = |key: &str, position, (signature, body)| {
        Item::new(
            ItemKey::from(key),
            declaration(Position(position), signature, body),
        )
    };
    Program::new(arena, vec![
        item(
            "hole",
            0,
            (Maybe::Present(universe), Maybe::Absent(body::Absent::Hole)),
        ),
        item(
            "waiting",
            1,
            (Maybe::Present(decoded), Maybe::Present(zero)),
        ),
        Item::new(
            reader,
            declaration(
                Position(2),
                Maybe::Present(decoded),
                Maybe::Present(waiting),
            ),
        ),
    ])
    .expect("positions ascend")
}

/// A resume adopts the suspended `waiting` and judges a renamed `reader` that
/// reads it. The adopted suspension is seated from its report, so the reader
/// keeps the report that a check from scratch gives it.
#[test]
fn an_adopted_suspension_is_seated_for_the_reader_that_the_resume_judges()
{
    let base = checked(&mut waiting_and(ItemKey::from("reader")));
    let mut edited = waiting_and(ItemKey::from("renamed"));
    let resumed = crate::checkpoint::resume_from(&base, &mut edited).expect("the order builds");
    let census = resumed.census();
    assert_eq!(
        (usize::from(census.adopted), usize::from(census.judged)),
        (2, 1),
        "the resume adopts the hole and the suspension and judges the renamed reader"
    );
    let from_scratch = checked(&mut waiting_and(ItemKey::from("renamed")));
    let (Some(resumed_reader), Some(scratch_reader)) = (
        resumed.checkpoints().items().last(),
        from_scratch.items().last(),
    )
    else {
        panic!("each set keeps the reader");
    };
    let (Maybe::Present(resumed_report), Maybe::Present(scratch_report)) =
        (resumed_reader.report(), scratch_reader.report())
    else {
        panic!("the reader keeps a report in each set");
    };
    assert!(
        matches!(scratch_report.suspension(), Maybe::Present(_)),
        "the reader is suspended on the hole"
    );
    assert_eq!(
        resumed_report, scratch_report,
        "the resumed reader keeps the report that a check from scratch gives it"
    );
}
