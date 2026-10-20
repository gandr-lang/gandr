use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec;
use alloc::vec::Vec;

use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::DataSignature;
use gandr_core_term::LinearUse;
use gandr_core_term::LinearZone;
use gandr_core_term::Sort;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::effect::EffectRow;
use gandr_core_term::effect::capability::CapabilityGrade;
use gandr_core_term::effect::capability::Region;
use gandr_core_term::session::PayloadCount;
use gandr_core_term::session::Protocol;
use gandr_core_term::session::ProtocolState;
use gandr_core_term::session::ProtocolSyntax;
use gandr_core_term::session::SessionType;
use gandr_core_term::world::World;
use gandr_core_term::world::WorldForm;
use gandr_core_term::world::WorldType;
use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldLabel;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::Literal;
use gandr_kernel_term::SealExtent;
use gandr_kernel_term::Stage;
use gandr_kernel_term::StageId;
use gandr_kernel_term::StringLiteral;
use quenchant_shape::shape::Maybe;

use super::Crossed;
use super::Crossing;
use super::Entry;
use super::HostEntry;
use super::LocatedDefect;
use super::Mobility;
use super::Predicate;
use super::WorldMove;
use super::crosses;
use crate::CheckBudget;
use crate::CheckRefusal;
use crate::CheckingContext;
use crate::CoreNode;
use crate::Declaration;
use crate::DeclarationContent;
use crate::Judged;
use crate::OriginToken;
use crate::TermNode;
use crate::TypeNode;
use crate::Typings;
use crate::Verdict;
use crate::body;
use crate::bridge;
use crate::check_module;
use crate::declaration::AbstractType;
use crate::seal::ComponentOrdinal;
use crate::seal::SealSite;
use crate::seal::SealingSite;
use crate::session::Capture;
use crate::type_module;

/// An admission position in a fixture module.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct At(usize);

impl At
{
    /// The position as a constant.
    ///
    /// # Specification
    /// trivial.
    fn constant(self) -> ConstantIndex
    {
        ConstantIndex::from(self.0)
    }

    /// The origin of the declaration at the position.
    ///
    /// # Specification
    /// trivial.
    fn origin(self) -> OriginToken
    {
        OriginToken::from(self.0)
    }
}

/// The spelling of a text literal.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Spelled(&'static str);

/// The position of the operator's world declaration.
const OPERATOR: At = At(0);

/// The position of the seat's world declaration.
const SEAT: At = At(1);

/// The world the declaration at `position` declares.
///
/// # Specification
/// trivial.
fn world(position: At) -> World
{
    World::Declared(position.constant())
}

/// `world operator ;` and `world seat ;`, at their positions.
///
/// # Specification
/// trivial.
fn worlds() -> [Declaration; 2]
{
    [OPERATOR, SEAT].map(|position| Declaration::world(position.constant(), position.origin()))
}

/// The operator's entry: at its own world, holding one capability to the
/// seat's.
///
/// # Specification
/// trivial.
fn operating() -> Entry
{
    Entry::new(world(OPERATOR), vec![world(SEAT)])
}

/// The text literal `spelled`.
///
/// # Specification
/// trivial.
fn text(
    arena: &mut CoreArena,
    Spelled(spelled): Spelled,
) -> ValueId
{
    arena.value_literal(Literal::Text(StringLiteral::new(String::from(spelled))))
}

/// `migrate[w] { body }`, `w` the world declared at `to`.
///
/// # Specification
/// trivial.
fn migrate(
    arena: &mut CoreArena,
    to: At,
    body: ComputationId,
) -> ComputationId
{
    arena.computation_world(WorldForm::Migrate {
        world: world(to),
        body,
    })
}

/// The declaration at `position` of type `U (F result)` whose body is
/// `thunk { body }`.
///
/// # Specification
/// trivial.
fn entry_point(
    arena: &mut CoreArena,
    position: At,
    result: ValueTypeId,
    body: ComputationId,
) -> Declaration
{
    let returner = arena.comp_type_returner(result);
    let declared = arena.value_type_thunk(returner);
    let suspended = arena.value_thunk(body);
    Declaration::new(
        position.constant(),
        Maybe::Present(declared),
        Maybe::Present(suspended),
        position.origin(),
    )
}

/// The body of the value declaration `declaration`.
///
/// # Specification
/// trivial.
fn body_of(declaration: &Declaration) -> ValueId
{
    match *declaration.content() {
        DeclarationContent::Value {
            body: Maybe::Present(body),
            ..
        } => body,
        DeclarationContent::Value { .. }
        | DeclarationContent::Data(_)
        | DeclarationContent::Codata(_)
        | DeclarationContent::Abstract(_)
        | DeclarationContent::World => panic!("the fixture reads the body of a defined value"),
    }
}

/// The declaration at `position` owing a value of `declared`.
///
/// # Specification
/// trivial.
fn owed(
    position: At,
    declared: ValueTypeId,
) -> Declaration
{
    Declaration::new(
        position.constant(),
        Maybe::Present(declared),
        Maybe::Absent(body::Absent::Hole),
        position.origin(),
    )
}

/// The abstract type at `position`, sealing `representation` at the value
/// universe for no later position, marked `mobility`.
///
/// # Specification
/// trivial.
fn sealed(
    arena: &mut CoreArena,
    position: At,
    representation: ValueTypeId,
    mobility: Mobility,
) -> Declaration
{
    let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    Declaration::abstract_type(
        position.constant(),
        AbstractType::new(
            small,
            representation,
            SealExtent::from(0_usize),
            SealSite::new(
                SealingSite::from(position.0),
                ComponentOrdinal::from(0_usize),
            ),
        )
        .marked(mobility),
        position.origin(),
    )
}

/// The verdicts of `module`, judged in order under the host's entry `host`.
///
/// # Specification
/// trivial.
fn verdicts(
    arena: &mut CoreArena,
    host: HostEntry,
    module: &[Declaration],
) -> Vec<Verdict>
{
    let mut context = CheckingContext::new(arena, CheckBudget::DEFAULT);
    context.enter_at(host);
    check_module(&mut context, module)
        .judged()
        .iter()
        .map(Judged::verdict)
        .collect()
}

/// The refusal of a located judgement at `at`.
///
/// # Specification
/// trivial.
const fn located(
    at: CoreNode,
    defect: LocatedDefect,
) -> Verdict
{
    Verdict::Refused(CheckRefusal::Located { at, defect })
}

/// The node of the computation `term`.
///
/// # Specification
/// trivial.
const fn computation(term: ComputationId) -> CoreNode
{
    CoreNode::Term(TermNode::Computation(term))
}

/// The node of the value `term`.
///
/// # Specification
/// trivial.
const fn value(term: ValueId) -> CoreNode
{
    CoreNode::Term(TermNode::Value(term))
}

/// The pure session `end`.
///
/// # Specification
/// trivial.
fn ended(arena: &mut CoreArena) -> ValueTypeId
{
    let protocol = Protocol::new(
        vec![ProtocolSyntax::End],
        ProtocolState::from(0_usize),
        PayloadCount::from(0_usize),
    )
    .unwrap();
    let session = SessionType::new(Arc::new(protocol), Arc::from([])).unwrap();
    arena.value_type_session(session)
}

#[test]
fn mobility_is_decided_on_every_former()
{
    let mut arena = CoreArena::new();
    let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let integer = arena.value_type_base(BaseType::Integer);
    let string = arena.value_type_base(BaseType::String);
    let unit = arena.value_type_unit();
    let returns = arena.comp_type_returner(string);
    let thunk = arena.value_type_thunk(returns);
    let pair = arena.value_type_product(&[integer, string]);
    let holding = arena.value_type_product(&[integer, thunk]);
    let either = arena.value_type_sum(&[unit, string]);
    let either_holding = arena.value_type_sum(&[unit, thunk]);
    let record = arena.value_type_record(BTreeMap::from([(
        FieldLabel::from(String::from("report")),
        string,
    )]));
    let record_holding = arena.value_type_record(BTreeMap::from([(
        FieldLabel::from(String::from("later")),
        thunk,
    )]));
    let list = arena.value_type_list(string);
    let list_holding = arena.value_type_list(thunk);
    let one = Level::zero().succ().unwrap();
    let lifted = arena.value_type_lift(string, one.clone());
    let staged = arena.value_type_staged(integer, Stage::At(StageId::from(0_usize)));
    let sigma = arena.value_type_sigma(integer, string);
    let sigma_holding = arena.value_type_sigma(integer, thunk);
    let handle = arena.value_type_world(WorldType::At {
        inner: string,
        world: world(SEAT),
    });
    let handle_holding = arena.value_type_world(WorldType::At {
        inner: thunk,
        world: world(SEAT),
    });
    let session = ended(&mut arena);
    let endpoint_handle = arena.value_type_world(WorldType::At {
        inner: session,
        world: world(SEAT),
    });
    let capability = arena.value_type_world(WorldType::Capability(world(SEAT)));
    let effects =
        arena.value_type_capability(EffectRow::default(), CapabilityGrade::Durable, Region::Held);
    let stack = arena.value_type_stack(returns, returns);
    let code = arena.value_quote(integer);
    let static_pi = arena.value_type_static_pi(small, small);
    let path_universe = arena.value_type_path_universe(code, code);
    let path = arena.value_type_path(integer, code, code);
    let flow = arena.value_type_flow(small, code, code);
    let run = arena.value_type_run(code);
    let unknown = arena.value_type_unknown();
    let decoded = arena.value_type_element(code, Level::zero());
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let opaque = arena.value_type_element(bound, Level::zero());
    // `Box (a : Type) = box (El a)` at 0, `Nat = zero | succ Nat` at 1,
    // `Later = later (U (F String))` at 2, `Dependent = mk (a : Type, x : El a)`
    // at 3, an unmarked abstract integer at 4 and a marked one at 5.
    let boxes = Arc::new(DataSignature::new(vec![small], vec![vec![opaque]], small));
    let thunk_code = arena.value_quote(thunk);
    let boxed = arena.value_type_data(ConstantIndex::from(0_usize), vec![code]);
    let boxed_holding = arena.value_type_data(ConstantIndex::from(0_usize), vec![thunk_code]);
    let nat = arena.value_type_data(ConstantIndex::from(1_usize), vec![]);
    let nats = Arc::new(DataSignature::new(vec![], vec![vec![], vec![nat]], small));
    let laters = Arc::new(DataSignature::new(vec![], vec![vec![thunk]], small));
    let later = arena.value_type_data(ConstantIndex::from(2_usize), vec![]);
    let one_universe = arena.value_type_universe(Sort::Ground(GroundSort::Value), one);
    let dependents = Arc::new(DataSignature::new(
        vec![],
        vec![vec![small, opaque]],
        one_universe,
    ));
    let dependent = arena.value_type_data(ConstantIndex::from(3_usize), vec![]);
    let site =
        |position| SealSite::new(SealingSite::from(position), ComponentOrdinal::from(0_usize));
    let unmarked = AbstractType::new(small, integer, SealExtent::from(0_usize), site(4_usize));
    let marked = AbstractType::new(small, integer, SealExtent::from(0_usize), site(5_usize))
        .marked(Mobility::Mobile);
    let unmarked_atom = arena.value_type_abstract(ConstantIndex::from(4_usize));
    let marked_atom = arena.value_type_abstract(ConstantIndex::from(5_usize));
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    for (position, signature) in [boxes, nats, laters, dependents].into_iter().enumerate() {
        context
            .adopt_data(ConstantIndex::from(position), signature)
            .expect("the fixture's datatypes form");
    }
    context
        .adopt_abstract(ConstantIndex::from(4_usize), unmarked)
        .expect("the unmarked atom forms");
    context
        .adopt_abstract(ConstantIndex::from(5_usize), marked)
        .expect("the marked atom forms");
    context.binders().open(Zone::Intuitionistic, small);
    let stays = |former, predicate| Crossing::Stays { former, predicate };
    let mobile = Predicate::Mobile;
    let decisions = [
        (integer, Crossing::Crosses, "an integer"),
        (string, Crossing::Crosses, "a string"),
        (unit, Crossing::Crosses, "the unit"),
        (pair, Crossing::Crosses, "a product of crossing components"),
        (holding, stays(thunk, mobile), "a product holding a thunk"),
        (either, Crossing::Crosses, "a sum of crossing summands"),
        (
            either_holding,
            stays(thunk, mobile),
            "a sum holding a thunk",
        ),
        (record, Crossing::Crosses, "a record of crossing fields"),
        (
            record_holding,
            stays(thunk, mobile),
            "a record holding a thunk",
        ),
        (list, Crossing::Crosses, "a list of a crossing element"),
        (list_holding, stays(thunk, mobile), "a list of thunks"),
        (lifted, Crossing::Crosses, "a lift of a crossing type"),
        (staged, Crossing::Crosses, "a staged crossing type"),
        (sigma, Crossing::Crosses, "a sigma of crossing components"),
        (
            sigma_holding,
            stays(thunk, mobile),
            "a sigma holding a thunk",
        ),
        (
            handle,
            Crossing::Crosses,
            "a handle holding a crossing type",
        ),
        (
            handle_holding,
            stays(thunk, Predicate::Open),
            "a handle holding a thunk is mobile and not open",
        ),
        (
            endpoint_handle,
            stays(session, Predicate::Open),
            "a handle holding an endpoint",
        ),
        (
            boxed,
            Crossing::Crosses,
            "a datatype at a crossing argument",
        ),
        (
            boxed_holding,
            stays(thunk, mobile),
            "a datatype at a thunk argument",
        ),
        (
            nat,
            Crossing::Crosses,
            "a recursive datatype of crossing fields",
        ),
        (later, stays(thunk, mobile), "a datatype with a thunk field"),
        (
            marked_atom,
            Crossing::Crosses,
            "an atom its signature marks mobile",
        ),
        (
            unmarked_atom,
            stays(unmarked_atom, mobile),
            "an atom its signature leaves unmarked",
        ),
        (unknown, Crossing::Crosses, "the unknown type"),
        (decoded, Crossing::Crosses, "the decode of a crossing code"),
        (
            opaque,
            stays(opaque, mobile),
            "the decode of a code the judgement cannot read",
        ),
        (thunk, stays(thunk, mobile), "a thunk"),
        (stack, stays(stack, mobile), "a stack"),
        (session, stays(session, mobile), "an endpoint"),
        (effects, stays(effects, mobile), "an effect capability"),
        (capability, stays(capability, mobile), "a world capability"),
        (small, stays(small, mobile), "a universe"),
        (static_pi, stays(static_pi, mobile), "a static Pi"),
        (
            path_universe,
            stays(path_universe, mobile),
            "a path between codes",
        ),
        (path, stays(path, mobile), "a path"),
        (flow, stays(flow, mobile), "a flow"),
        (run, stays(run, mobile), "a recorded run"),
    ];
    for (ty, expected, what) in decisions {
        assert_eq!(crosses(&mut context, ty), Ok(expected), "{what}");
    }
    assert!(
        matches!(
            crosses(&mut context, dependent),
            Ok(Crossing::Stays {
                predicate: Predicate::Mobile,
                ..
            })
        ),
        "a datatype with a dependent field"
    );
}

#[test]
fn a_migration_consumes_its_capability_visibly()
{
    let mut arena = CoreArena::new();
    let string = arena.value_type_base(BaseType::String);
    let report = text(&mut arena, Spelled("report"));
    let returned = arena.computation_return(report);
    let migration = migrate(&mut arena, SEAT, returned);
    let [operator, seat] = worlds();
    let module = [
        operator,
        seat,
        entry_point(&mut arena, At(2), string, migration).entered(operating()),
    ];
    assert!(
        matches!(verdicts(&mut arena, HostEntry::Unbounded, &module)[..], [
            Verdict::Data,
            Verdict::Data,
            Verdict::Checked { .. }
        ]),
        "a migration holding its capability checks"
    );
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let typed = type_module(&mut context, &module);
    let moves = typed.get(&ConstantIndex::from(2_usize)).map(Typings::moves);
    let Some(
        &[
            WorldMove::Migrated {
                at,
                from,
                to,
                ref before,
                ref after,
            },
            WorldMove::Returned { at: back, to: home },
        ],
    ) = moves
    else {
        panic!("a typed run keeps one migration and its return: {moves:?}");
    };
    assert_eq!(
        (at, from, to, back, home),
        (
            migration,
            world(OPERATOR),
            world(SEAT),
            migration,
            world(OPERATOR)
        ),
        "the migration leaves the operator's world for the seat's and comes back"
    );
    let capability = Some(ValueType::World(WorldType::Capability(world(SEAT))));
    let read = |zone: &LinearZone| {
        zone.slots()
            .map(|(ty, used)| (context.arena().value_type(ty).cloned(), used))
            .collect::<Vec<_>>()
    };
    assert_eq!(
        read(before),
        [(capability.clone(), LinearUse::Available)],
        "the capability stands available before the migration"
    );
    assert_eq!(
        read(after),
        [(capability, LinearUse::Consumed)],
        "and is consumed by it"
    );
}

#[test]
fn a_second_migration_without_a_capability_is_refused()
{
    let mut arena = CoreArena::new();
    let string = arena.value_type_base(BaseType::String);
    let report = text(&mut arena, Spelled("report"));
    let again = text(&mut arena, Spelled("again"));
    let returned = arena.computation_return(report);
    let returned_again = arena.computation_return(again);
    let first = migrate(&mut arena, SEAT, returned);
    let second = migrate(&mut arena, SEAT, returned_again);
    let returns = arena.comp_type_returner(string);
    let ascribed = arena.computation_ascribe(first, returns);
    let twice = arena.computation_bind(ascribed, second);
    // `apply : U (U (F String) → F String)`, owed at 4, forced over a thunk
    // holding the migration.
    let suspended = arena.value_type_thunk(returns);
    let applying = arena.comp_type_arrow(suspended, returns);
    let apply = arena.value_type_thunk(applying);
    let applied = arena.value_constant(ConstantIndex::from(4_usize));
    let forced = arena.computation_force(applied);
    let inner = arena.value_thunk(first);
    let captured = arena.computation_application(forced, inner);
    let entered = arena.value_constant(ConstantIndex::from(3_usize));
    let reentered = arena.computation_force(entered);
    let [operator, seat] = worlds();
    let module = [
        operator,
        seat,
        entry_point(&mut arena, At(2), string, twice).entered(operating()),
        entry_point(&mut arena, At(3), string, twice)
            .entered(Entry::new(world(OPERATOR), vec![world(SEAT), world(SEAT)])),
        owed(At(4), apply),
        entry_point(&mut arena, At(5), string, captured).entered(operating()),
        entry_point(&mut arena, At(6), string, reentered),
    ];
    let verdicts = verdicts(&mut arena, HostEntry::Unbounded, &module);
    assert_eq!(
        verdicts.get(2),
        Some(&located(
            computation(second),
            LocatedDefect::CapabilityMissing { world: world(SEAT) }
        )),
        "the second migration finds the capability spent"
    );
    assert!(
        matches!(verdicts.get(3), Some(&Verdict::Checked { .. })),
        "an entry holding two capabilities migrates twice"
    );
    assert_eq!(
        verdicts.get(5),
        Some(&located(
            computation(first),
            LocatedDefect::CapabilityCaptured {
                world: world(SEAT),
                by: Capture::Thunk,
            }
        )),
        "a migration in a thunk the entry did not force may run other than once"
    );
    assert_eq!(
        verdicts.get(6),
        Some(&located(value(entered), LocatedDefect::EntryNamed {
            constant: ConstantIndex::from(3_usize),
        })),
        "an entry that spent a capability is no value another declaration may force"
    );
}

#[test]
fn a_stated_entry_is_bounded_by_the_host_s()
{
    let mut arena = CoreArena::new();
    let string = arena.value_type_base(BaseType::String);
    let report = text(&mut arena, Spelled("report"));
    let returned = arena.computation_return(report);
    let migration = migrate(&mut arena, SEAT, returned);
    let [operator, seat] = worlds();
    let stated = [
        Maybe::Absent(crate::declaration::entry::Absent::Unstated),
        Maybe::Present(operating()),
        Maybe::Present(Entry::new(world(SEAT), vec![])),
        Maybe::Present(Entry::new(world(OPERATOR), vec![world(SEAT), world(SEAT)])),
        Maybe::Present(Entry::new(world(OPERATOR), vec![])),
        Maybe::Present(Entry::new(world(OPERATOR), vec![world(At(2))])),
    ];
    let mut module = vec![operator, seat];
    for (position, entry) in (2_usize ..).zip(stated) {
        let declaration = entry_point(&mut arena, At(position), string, migration);
        module.push(match entry {
            Maybe::Present(entry) => declaration.entered(entry),
            Maybe::Absent(_) => declaration,
        });
    }
    let at_body = |position: usize| value(body_of(&module[position]));
    let missing = located(computation(migration), LocatedDefect::CapabilityMissing {
        world: world(SEAT),
    });
    let within = verdicts(&mut arena, HostEntry::Within(operating()), &module);
    assert!(
        matches!(within[2 ..], [
            Verdict::Checked { .. },
            Verdict::Checked { .. },
            _,
            _,
            _,
            _
        ]),
        "an entry stating none takes the host's, and one stating the host's holds it: {within:?}"
    );
    assert_eq!(
        within[4 ..],
        [
            located(at_body(4), LocatedDefect::EntryUngranted {
                constant: ConstantIndex::from(4_usize)
            }),
            located(at_body(5), LocatedDefect::EntryUngranted {
                constant: ConstantIndex::from(5_usize)
            }),
            missing,
            located(at_body(7), LocatedDefect::UndeclaredWorld {
                world: ConstantIndex::from(2_usize),
            }),
        ],
        "an entry at another home or claiming a capability twice is ungranted; one within the host's holds no more than it states, and none names a position that declares no world"
    );
    let unbounded = verdicts(&mut arena, HostEntry::Unbounded, &module);
    assert_eq!(
        unbounded.get(2),
        Some(&missing),
        "with no host entry, an entry stating none holds no capability"
    );
    assert!(
        matches!(unbounded.get(5), Some(&Verdict::Checked { .. })),
        "and a stated entry is taken as stated"
    );
    let unnamed = verdicts(&mut arena, HostEntry::Undeclared, &module);
    assert_eq!(
        unnamed.get(2),
        Some(&located(at_body(2), LocatedDefect::HostWorldUndeclared)),
        "a host naming a world the source does not declare grants nothing"
    );
}

#[test]
fn a_located_hypothesis_is_usable_only_at_its_world()
{
    let mut arena = CoreArena::new();
    let string = arena.value_type_base(BaseType::String);
    let report = text(&mut arena, Spelled("report"));
    let held = arena.computation_world(WorldForm::Hold { value: report });
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let read = arena.computation_return(bound);
    let read_here = arena.computation_world(WorldForm::Leta {
        value: bound,
        body: read,
    });
    let migration = migrate(&mut arena, SEAT, read);
    let read_there = arena.computation_world(WorldForm::Leta {
        value: bound,
        body: migration,
    });
    let here = arena.computation_bind(held, read_here);
    let there = arena.computation_bind(held, read_there);
    let [operator, seat] = worlds();
    let module = [
        operator,
        seat,
        entry_point(&mut arena, At(2), string, here).entered(operating()),
        entry_point(&mut arena, At(3), string, there).entered(operating()),
    ];
    let verdicts = verdicts(&mut arena, HostEntry::Unbounded, &module);
    assert!(
        matches!(verdicts.get(2), Some(&Verdict::Checked { .. })),
        "a report held and opened at the operator's world is read there"
    );
    assert_eq!(
        verdicts.get(3),
        Some(&located(value(bound), LocatedDefect::Elsewhere {
            bound: world(OPERATOR),
        })),
        "and not at the seat's"
    );
}

#[test]
fn hold_cannot_fabricate_a_remote_value()
{
    let mut arena = CoreArena::new();
    let string = arena.value_type_base(BaseType::String);
    let report = text(&mut arena, Spelled("report"));
    let held = arena.computation_world(WorldForm::Hold { value: report });
    let remote = arena.value_type_world(WorldType::At {
        inner: string,
        world: world(SEAT),
    });
    let local = arena.value_type_world(WorldType::At {
        inner: string,
        world: world(OPERATOR),
    });
    let bare = Entry::new(world(OPERATOR), vec![]);
    let [operator, seat] = worlds();
    let module = [
        operator,
        seat,
        entry_point(&mut arena, At(2), remote, held).entered(bare.clone()),
        entry_point(&mut arena, At(3), local, held).entered(bare),
        entry_point(&mut arena, At(4), local, held),
    ];
    let verdicts = verdicts(&mut arena, HostEntry::Unbounded, &module);
    assert_eq!(
        verdicts.get(2),
        Some(&located(computation(held), LocatedDefect::HoldElsewhere {
            wanted: world(SEAT),
        })),
        "a hold at the operator's world makes no handle at the seat's"
    );
    assert!(
        matches!(verdicts.get(3), Some(&Verdict::Checked { .. })),
        "it makes one at its own"
    );
    assert_eq!(
        verdicts.get(4),
        Some(&located(computation(held), LocatedDefect::Unlocated)),
        "and at the host's world, which is no locus, none"
    );
}

#[test]
fn a_report_crosses_and_an_endpoint_does_not()
{
    let mut arena = CoreArena::new();
    let string = arena.value_type_base(BaseType::String);
    let report = text(&mut arena, Spelled("report"));
    let returned = arena.computation_return(report);
    let reported = migrate(&mut arena, SEAT, returned);
    let returns = arena.comp_type_returner(string);
    let later = arena.value_type_thunk(returns);
    let suspended = arena.value_thunk(returned);
    let returned_later = arena.computation_return(suspended);
    let deferred = migrate(&mut arena, SEAT, returned_later);
    let session = ended(&mut arena);
    let endpoint_handle = arena.value_type_world(WorldType::At {
        inner: session,
        world: world(SEAT),
    });
    let [operator, seat] = worlds();
    let module = [
        operator,
        seat,
        entry_point(&mut arena, At(2), string, reported).entered(operating()),
        entry_point(&mut arena, At(3), later, deferred).entered(operating()),
    ];
    let verdicts = verdicts(&mut arena, HostEntry::Unbounded, &module);
    assert!(
        matches!(verdicts.get(2), Some(&Verdict::Checked { .. })),
        "a migration returning a report checks"
    );
    assert_eq!(
        verdicts.get(3),
        Some(&located(computation(deferred), LocatedDefect::Immobile {
            crossed: Crossed::Result,
            ty: later,
            former: later,
            predicate: Predicate::Mobile,
        })),
        "one returning a thunk is refused by name"
    );
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    assert_eq!(
        crosses(&mut context, session),
        Ok(Crossing::Stays {
            former: session,
            predicate: Predicate::Mobile,
        }),
        "an endpoint does not cross"
    );
    assert_eq!(
        crosses(&mut context, endpoint_handle),
        Ok(Crossing::Stays {
            former: session,
            predicate: Predicate::Open,
        }),
        "nor does a handle to one"
    );
}

#[test]
fn an_unmarked_abstract_payload_is_immobile()
{
    let mut arena = CoreArena::new();
    let string = arena.value_type_base(BaseType::String);
    let [operator, seat] = worlds();
    let unmarked = sealed(&mut arena, At(2), string, Mobility::Immobile);
    let marked = sealed(&mut arena, At(3), string, Mobility::Mobile);
    let unmarked_atom = arena.value_type_abstract(ConstantIndex::from(2_usize));
    let marked_atom = arena.value_type_abstract(ConstantIndex::from(3_usize));
    let [unmarked_payload, marked_payload] =
        [4_usize, 5].map(|position| arena.value_constant(ConstantIndex::from(position)));
    let [unmarked_returned, marked_returned] =
        [unmarked_payload, marked_payload].map(|payload| arena.computation_return(payload));
    let unmarked_migration = migrate(&mut arena, SEAT, unmarked_returned);
    let marked_migration = migrate(&mut arena, SEAT, marked_returned);
    let module = [
        operator,
        seat,
        unmarked,
        marked,
        owed(At(4), unmarked_atom),
        owed(At(5), marked_atom),
        entry_point(&mut arena, At(6), unmarked_atom, unmarked_migration).entered(operating()),
        entry_point(&mut arena, At(7), marked_atom, marked_migration).entered(operating()),
    ];
    let verdicts = verdicts(&mut arena, HostEntry::Unbounded, &module);
    assert_eq!(
        verdicts.get(6),
        Some(&located(
            computation(unmarked_migration),
            LocatedDefect::Immobile {
                crossed: Crossed::Result,
                ty: unmarked_atom,
                former: unmarked_atom,
                predicate: Predicate::Mobile,
            }
        )),
        "an unmarked atom stays where it was made, whatever it stands for"
    );
    assert!(
        matches!(verdicts.get(7), Some(&Verdict::Checked { .. })),
        "a marked one crosses"
    );
}

#[test]
fn a_mobility_mark_over_an_immobile_representation_is_refused_at_sealing()
{
    let mut arena = CoreArena::new();
    let string = arena.value_type_base(BaseType::String);
    let returns = arena.comp_type_returner(string);
    let thunk = arena.value_type_thunk(returns);
    let module = [
        sealed(&mut arena, At(0), thunk, Mobility::Mobile),
        sealed(&mut arena, At(1), string, Mobility::Mobile),
        sealed(&mut arena, At(2), thunk, Mobility::Immobile),
    ];
    let verdicts = verdicts(&mut arena, HostEntry::Unbounded, &module);
    assert_eq!(
        verdicts,
        [
            located(
                CoreNode::Type(TypeNode::Value(thunk)),
                LocatedDefect::MarkUnfounded {
                    atom: ConstantIndex::from(0_usize),
                    former: thunk,
                    predicate: Predicate::Mobile,
                }
            ),
            Verdict::Data,
            Verdict::Data,
        ],
        "a mobile mark over a thunk is refused where the representation is visible; over a string, or unmarked, it seals"
    );
}

#[test]
fn an_undeclared_world_is_refused()
{
    let mut arena = CoreArena::new();
    let string = arena.value_type_base(BaseType::String);
    let report = text(&mut arena, Spelled("report"));
    let returned = arena.computation_return(report);
    let migration = migrate(&mut arena, At(1), returned);
    let held = arena.computation_world(WorldForm::Hold { value: report });
    let nowhere = arena.value_type_world(WorldType::At {
        inner: string,
        world: world(At(1)),
    });
    let [operator, _] = worlds();
    let module = [
        operator,
        Declaration::new(
            ConstantIndex::from(1_usize),
            Maybe::Present(string),
            Maybe::Present(report),
            OriginToken::from(1_usize),
        ),
        entry_point(&mut arena, At(2), nowhere, held).entered(Entry::new(world(OPERATOR), vec![])),
        entry_point(&mut arena, At(3), string, migration)
            .entered(Entry::new(world(OPERATOR), vec![])),
        entry_point(&mut arena, At(4), string, returned).entered(Entry::new(world(At(1)), vec![])),
    ];
    let undeclared = LocatedDefect::UndeclaredWorld {
        world: ConstantIndex::from(1_usize),
    };
    assert_eq!(
        verdicts(&mut arena, HostEntry::Unbounded, &module)[2 ..],
        [
            located(CoreNode::Type(TypeNode::Value(nowhere)), undeclared),
            located(computation(migration), undeclared),
            located(value(body_of(&module[4])), undeclared),
        ],
        "a handle, a migration and an entry naming a position no world declaration holds are refused"
    );
}

#[test]
fn readmission_refuses_a_located_declaration_by_name()
{
    let mut arena = CoreArena::new();
    let string = arena.value_type_base(BaseType::String);
    let report = text(&mut arena, Spelled("report"));
    let returned = arena.computation_return(report);
    let migration = migrate(&mut arena, SEAT, returned);
    let [operator, seat] = worlds();
    let module = [
        operator,
        seat,
        entry_point(&mut arena, At(2), string, migration).entered(operating()),
        Declaration::new(
            ConstantIndex::from(3_usize),
            Maybe::Present(string),
            Maybe::Present(report),
            OriginToken::from(3_usize),
        ),
    ];
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let report = check_module(&mut context, &module);
    let readmission = bridge::readmit(&mut arena, &report);
    let outcomes: Vec<_> = readmission
        .readmitted()
        .iter()
        .map(bridge::Readmitted::outcome)
        .collect();
    assert!(
        matches!(
            outcomes[..],
            [
                &bridge::Outcome::Static,
                &bridge::Outcome::Static,
                &bridge::Outcome::Refused(bridge::Refusal::Located { at }),
                &bridge::Outcome::Defined { .. },
            ] if at == computation(migration)
        ),
        "the worlds stay on the checker's side, the located declaration is refused at its migration, and the rest is readmitted: {outcomes:?}"
    );
}

#[test]
fn an_entry_reads_its_home_then_its_capabilities()
{
    let named = [OPERATOR, SEAT, SEAT].map(At::constant);
    assert_eq!(
        Entry::declared(&named),
        Maybe::Present(Entry::new(world(OPERATOR), vec![world(SEAT), world(SEAT)])),
        "the first name is the home and each later name one capability, in written order"
    );
    assert_eq!(
        Entry::declared(&named[.. 1]),
        Maybe::Present(Entry::new(world(OPERATOR), vec![])),
        "one name is a home holding no capability"
    );
    assert_eq!(
        Entry::declared(&[]),
        Maybe::Absent(crate::declaration::entry::Absent::Unstated),
        "no name states no entry"
    );
}
