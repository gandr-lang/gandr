//! A located program through the incremental checker: its items persist by
//! content, a resume adopts what it judged before, and a changed home or a
//! changed grant judges again exactly the items it reaches.

use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;

use gandr_core_checker::CheckBudget;
use gandr_core_checker::Declaration;
use gandr_core_checker::OriginToken;
use gandr_core_checker::worlds::Entry;
use gandr_core_checker::worlds::HostEntry;
use gandr_core_incremental::Adoption;
use gandr_core_incremental::Item;
use gandr_core_incremental::ItemKey;
use gandr_core_incremental::Program;
use gandr_core_incremental::Typing;
use gandr_core_incremental::check_program;
use gandr_core_incremental::decode_checkpoints;
use gandr_core_incremental::encode_checkpoints;
use gandr_core_incremental::resume;
use gandr_core_incremental::resume_from;
use gandr_core_term::CoreArena;
use gandr_core_term::effect::EffectRow;
use gandr_core_term::world::World;
use gandr_core_term::world::WorldForm;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::Literal;
use gandr_kernel_term::StringLiteral;
use quenchant_shape::shape::Maybe;

/// The fixture's items, by admission position: the operator's world, the
/// seat's world, a report homed where its entry states, a reader of the
/// report that states no entry, an entry that migrates to the seat, and an
/// unrelated value that states no entry.
const NAMES: [&str; 6] = ["operator", "seat", "report", "read", "run", "other"];

/// The operator's world, which the first declaration declares.
///
/// # Specification
/// trivial.
fn operator() -> World
{
    World::Declared(ConstantIndex::from(0_usize))
}

/// The seat's world, which the second declaration declares.
///
/// # Specification
/// trivial.
fn seat() -> World
{
    World::Declared(ConstantIndex::from(1_usize))
}

/// The operator's entry: at the operator's world, holding one capability for
/// the seat's.
///
/// # Specification
/// trivial.
fn operating() -> Entry
{
    Entry::new(operator(), vec![seat()])
}

/// The fixture, its report homed at `home`, under the host's entry `host`.
///
/// # Specification
/// trivial.
fn located(
    home: World,
    host: HostEntry,
) -> Program
{
    let mut arena = CoreArena::new();
    let string = arena.value_type_base(BaseType::String);
    let text = |arena: &mut CoreArena, spelled: &str| {
        arena.value_literal(Literal::Text(StringLiteral::new(String::from(spelled))))
    };
    let value = |constant: usize, body| {
        Declaration::new(
            ConstantIndex::from(constant),
            Maybe::Present(string),
            Maybe::Present(body),
            OriginToken::from(constant),
        )
    };
    let report = text(&mut arena, "report");
    let named = arena.value_constant(ConstantIndex::from(2_usize));
    let sent = text(&mut arena, "sent");
    let returned = arena.computation_return(sent);
    let migration = arena.computation_world(WorldForm::Migrate {
        world: seat(),
        body: returned,
    });
    let returner = arena.comp_type_returner(string);
    let suspended = arena.value_type_thunk(returner);
    let run = arena.value_thunk(migration);
    let other = text(&mut arena, "other");
    let declarations = [
        Declaration::world(
            ConstantIndex::from(0_usize),
            EffectRow::EMPTY,
            OriginToken::from(0_usize),
        ),
        Declaration::world(
            ConstantIndex::from(1_usize),
            EffectRow::EMPTY,
            OriginToken::from(1_usize),
        ),
        value(2, report).entered(Entry::new(home, Vec::new())),
        value(3, named),
        Declaration::new(
            ConstantIndex::from(4_usize),
            Maybe::Present(suspended),
            Maybe::Present(run),
            OriginToken::from(4_usize),
        )
        .entered(operating()),
        value(5, other),
    ];
    let items = NAMES
        .iter()
        .zip(declarations)
        .map(|(&name, declaration)| Item::new(ItemKey::from(name), declaration))
        .collect();
    let mut program = Program::new(arena, items).expect("the positions ascend");
    program.enter_at(host);
    program
}

/// The typings a fresh pass over `program` gives.
///
/// # Specification
/// trivial.
fn fresh(program: &Program) -> Vec<Typing>
{
    check_program(&mut program.clone(), CheckBudget::DEFAULT)
        .expect("the fresh pass runs")
        .typings()
        .cloned()
        .collect()
}

/// The names of the items `adoptions` marks judged, in order.
///
/// # Specification
/// trivial.
fn judged(adoptions: &[Adoption]) -> Vec<String>
{
    NAMES
        .iter()
        .zip(adoptions)
        .filter(|&(_, &adoption)| adoption == Adoption::Judged)
        .map(|(&name, _)| String::from(name))
        .collect()
}

/// #3381: a located program persists by content. Each item's checkpoint
/// encodes, the bytes decode to the same checkpoints, and a resume from the
/// decoded checkpoints adopts every item with the verdicts a fresh pass
/// gives: the entry that migrates checks, and spends its capability.
#[test]
fn a_located_program_persists_and_judges_alike_3381()
{
    let mut program = located(operator(), HostEntry::Unbounded);
    let checked = check_program(&mut program, CheckBudget::DEFAULT).expect("the pass runs");
    assert!(
        checked
            .typings()
            .all(|typing| matches!(*typing, Typing::Data | Typing::Checked { .. })),
        "every item of the fixture is admitted: {:?}",
        checked.typings().collect::<Vec<_>>()
    );
    let bytes = encode_checkpoints(checked.checkpoints()).expect("every checkpoint encodes");
    let decoded = decode_checkpoints(&bytes).expect("the canonical bytes decode");
    assert_eq!(
        decoded,
        *checked.checkpoints(),
        "the round trip keeps the checkpoints exactly"
    );
    let mut again = located(operator(), HostEntry::Unbounded);
    let resumed = resume_from(&decoded, &mut again).expect("the decoded checkpoints resume");
    assert_eq!(
        judged(resumed.adoptions()),
        Vec::<&str>::new(),
        "a resume from the persisted checkpoints adopts every item"
    );
    assert_eq!(
        resumed.typings().cloned().collect::<Vec<_>>(),
        fresh(&again),
        "and gives the verdicts a fresh pass gives"
    );
}

/// #3381: a declaration whose home changes is judged again, and so is each
/// reader of it: the register's answer it read beside the declaration's type
/// changed. The worlds, the migrating entry and the unrelated value are
/// adopted, and every verdict is the one a fresh pass gives.
#[test]
fn a_changed_home_judges_its_readers_again_3381()
{
    let mut base = located(operator(), HostEntry::Unbounded);
    let checked = check_program(&mut base, CheckBudget::DEFAULT).expect("the pass runs");
    let mut moved = located(seat(), HostEntry::Unbounded);
    let resumed = resume(checked, &mut moved).expect("the moved program resumes");
    assert_eq!(
        judged(resumed.adoptions()),
        ["report", "read"],
        "the moved report and its reader are judged again, and nothing else"
    );
    assert_eq!(
        resumed.typings().cloned().collect::<Vec<_>>(),
        fresh(&moved),
        "every verdict is the one a fresh pass gives"
    );
}

/// #3381: under a changed grant, each value declaration whose resolved entry
/// moves is judged again: those that state no entry take the host's. No
/// world is judged again, and no declaration whose stated entry stays within
/// the grant is judged again. Every verdict is the one a fresh pass under
/// the grant gives.
#[test]
fn a_changed_grant_judges_again_each_entry_it_moves_3381()
{
    let mut base = located(operator(), HostEntry::Unbounded);
    let checked = check_program(&mut base, CheckBudget::DEFAULT).expect("the pass runs");
    let mut granted = located(operator(), HostEntry::Within(operating()));
    let resumed = resume(checked, &mut granted).expect("the granted program resumes");
    assert_eq!(
        judged(resumed.adoptions()),
        ["read", "other"],
        "the two declarations that state no entry move to the grant's, and nothing else"
    );
    assert_eq!(
        resumed.typings().cloned().collect::<Vec<_>>(),
        fresh(&granted),
        "every verdict is the one a fresh pass under the grant gives"
    );
}
