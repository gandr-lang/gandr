use alloc::vec;

use gandr_core_term::CoreArena;
use gandr_core_term::Sort;
use gandr_core_term::Zone;
use gandr_core_term::hole::HoleId;
use gandr_core_term::hole::NominationIndex;
use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::GroundSort;
use quenchant_shape::shape::Maybe;

use super::elaborated;
use super::written;
use crate::content::ArenaNode;
use crate::content::TypeContent;
use crate::fixture::Digits;
use crate::fixture::Position;
use crate::fixture::checked;
use crate::fixture::declaration;
use crate::fixture::integer;
use crate::region::Item;
use crate::region::ItemKey;
use crate::region::Program;

/// The call of the identity that omits its implicit enters elaborated, its
/// implicit filled in its body; the identity enters as written. The pass
/// keeps the filled body as content and no other part, and a seat mints the
/// body into the program's arena as a node of that content.
#[test]
fn an_elaborated_item_keeps_its_filled_body_and_mints_it_back()
{
    // def id       : U ((a : Type) -> El a -> F (El a)) = thunk λ λ. return x ;
    // def omitting : U (F Integer) = thunk ((force id) ?a) 0 ;
    let mut arena = CoreArena::new();
    let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let element = arena.value_type_element(bound, Level::zero());
    let returns_element = arena.comp_type_returner(element);
    let arrow = arena.comp_type_arrow(element, returns_element);
    let polymorphic = arena.comp_type_pi(small, arrow);
    let identity_type = arena.value_type_thunk(polymorphic);
    let returned = arena.computation_return(bound);
    let inner = arena.computation_lambda(returned);
    let outer = arena.computation_lambda(inner);
    let identity = arena.value_thunk(outer);
    let integer_type = arena.value_type_base(BaseType::Integer);
    let returns_integer = arena.comp_type_returner(integer_type);
    let suspended = arena.value_type_thunk(returns_integer);
    let nominated = arena.value_hole(
        HoleId::nominated(NominationIndex::from(0_u32)).expect("the first nominated name"),
    );
    let zero = arena.value_literal(integer(Digits("0")));
    let named = arena.value_constant(ConstantIndex::from(0_usize));
    let head = arena.computation_force(named);
    let instantiated = arena.computation_application(head, nominated);
    let applied = arena.computation_application(instantiated, zero);
    let omitting = arena.value_thunk(applied);
    let mut program = Program::new(arena, vec![
        Item::new(
            ItemKey::from("id"),
            declaration(
                Position(0),
                Maybe::Present(identity_type),
                Maybe::Present(identity),
            ),
        ),
        Item::new(
            ItemKey::from("omitting"),
            declaration(
                Position(1),
                Maybe::Present(suspended),
                Maybe::Present(omitting),
            ),
        ),
    ])
    .expect("positions ascend");
    let checkpoints = checked(&mut program);
    let [ref as_written, ref filled] = *checkpoints.items()
    else {
        panic!("one checkpoint for each item");
    };
    assert_eq!(
        as_written.entry(),
        Maybe::Absent(elaborated::Absent::AsWritten),
        "the identity enters as written, so its checkpoint keeps no parts"
    );
    let Maybe::Present(entry) = filled.entry()
    else {
        panic!("the call enters elaborated: {:?}", filled.entry());
    };
    let Maybe::Present(body) = entry.body()
    else {
        panic!("the filled body is not the written body: {entry:?}");
    };
    assert_eq!(
        (entry.declared(), entry.stage(), entry.following()),
        (
            Maybe::Absent(written::Absent::Written),
            Maybe::Absent(written::Absent::Written),
            Maybe::Absent(written::Absent::Written)
        ),
        "the table holds the signature as written and binds no stage"
    );
    let Maybe::Present(seated) = entry.seat_in(&mut program)
    else {
        panic!("the parts seat in the program they came from");
    };
    let Maybe::Present(minted) = seated.body()
    else {
        panic!("the seat mints the body");
    };
    assert_eq!(
        TypeContent::of(program.arena(), program.layout(), ArenaNode::Value(minted)),
        *body,
        "the minted body has the content kept"
    );
}
