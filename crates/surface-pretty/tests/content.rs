//! The printer's two sources agree: a body read from the incremental
//! checker's content table spells as the same body read from its arena.

use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_checker::CheckBudget;
use gandr_core_checker::Declaration;
use gandr_core_checker::OriginToken;
use gandr_core_checker::body;
use gandr_core_checker::signature;
use gandr_core_incremental::DeclarationRoots;
use gandr_core_incremental::Item;
use gandr_core_incremental::ItemKey;
use gandr_core_incremental::NodeIndex;
use gandr_core_incremental::Program;
use gandr_core_incremental::check_program;
use gandr_core_term::ComponentCount;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::Sort;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::control::EffectClause;
use gandr_core_term::control::StackFrame;
use gandr_core_term::effect::EffectName;
use gandr_core_term::effect::EffectOp;
use gandr_core_term::effect::EffectRow;
use gandr_core_term::effect::EffectSig;
use gandr_core_term::hole::HoleId;
use gandr_core_term::memory::AccessMode;
use gandr_core_term::memory::HoldGrade;
use gandr_core_term::memory::MemoryForm;
use gandr_core_term::memory::Place;
use gandr_core_term::primitive::Arguments;
use gandr_core_term::primitive::PRELUDE;
use gandr_core_term::session::PayloadCount;
use gandr_core_term::session::PayloadSlot;
use gandr_core_term::session::Protocol;
use gandr_core_term::session::ProtocolState;
use gandr_core_term::session::ProtocolSyntax;
use gandr_core_term::session::SessionAction;
use gandr_core_term::session::SessionRelation;
use gandr_core_term::session::SessionType;
use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldLabel;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Sign;
use gandr_kernel_term::StringLiteral;
use gandr_kernel_term::Summand;
use gandr_surface_pretty::Constructors;
use gandr_surface_pretty::ContentSource;
use gandr_surface_pretty::CoreNode;
use gandr_surface_pretty::CoreSource;
use gandr_surface_pretty::Form;
use gandr_surface_pretty::Name;
use gandr_surface_pretty::PageWidth;
use gandr_surface_pretty::present_definition;
use quenchant_shape::shape::Maybe;

/// A closed body built into an arena.
type Body = fn(&mut CoreArena) -> ValueId;

/// What a corpus row builds, by name.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct What(&'static str);

/// The term `root` of `arena`, a value or a computation, spells the same at
/// the same fidelity whether read from the arena, its constants called by
/// `names`, or from the content table the incremental checker projects for
/// it, its constants the items of those names.
///
/// # Specification
/// - requires: `root` is a closed value or computation of `arena` whose
///   constants `names` all name, and which holds no world form, which content
///   keeps opaque.
/// - ensures: `root` is made the body of the last item of a program over a copy
///   of `arena`, a computation thunked first, each name before it an item with
///   no body at its admission position; that body written as a definition's
///   from the arena and from the last item's checked content, both at a hundred
///   columns in the explicit form, are the same text at the same fidelity.
/// - provides: the agreement the corpus and the goldens assert.
/// - panics: if the program does not ascend, the item's content holds no body,
///   the body does not project, either presentation refuses, or the two
///   disagree.
///
/// # Adequacy
/// - hypothesis: L3 — a corpus of every term former the arena builds without a
///   signature and of the types a quote carries, and the goldens' handlers,
///   sessions, memory forms, paths, flows and recorded runs, distinguish a
///   content former read as another and a component content leaves unread.
/// - witness: `tests::content::every_term_former_spells_from_its_content_as_from_its_arena`
/// - witness: `tests::goldens::a_fork_and_an_offer_keep_the_exits_they_end_in_815`
/// - witness: `tests::goldens::an_elaborated_body_prints_with_its_exits_elided`
/// - witness: `tests::goldens::a_continuation_is_resumed_by_its_call_941`
#[spec(requires: matches!(root, CoreNode::Value(_) | CoreNode::Computation(_)))]
pub fn agrees(
    arena: &CoreArena,
    names: &[Name<'_>],
    root: CoreNode,
)
{
    agrees_naming(arena, names, &Constructors::default(), root);
}

/// As [`agrees`], both sources naming constructors from `constructors`.
///
/// # Specification
/// - requires: as [`agrees`], every family `root` constructs or cases on named
///   by its item.
/// - ensures: as [`agrees`], each source naming constructors by family from
///   `constructors`.
/// - provides: the agreement over data the goldens assert.
/// - panics: as [`agrees`].
///
/// # Adequacy
/// - hypothesis: L3 — the goldens' constructors, data cases and words
///   distinguish a family resolved by item from one resolved by arena id.
/// - witness: `tests::goldens::an_elaborated_body_prints_with_its_exits_elided`
#[spec(requires: matches!(root, CoreNode::Value(_) | CoreNode::Computation(_)))]
pub fn agrees_naming(
    arena: &CoreArena,
    names: &[Name<'_>],
    constructors: &Constructors<'_>,
    root: CoreNode,
)
{
    let page = PageWidth::from(100_u32);
    let mut arena = arena.clone();
    let body = match root {
        CoreNode::Computation(computation) => arena.value_thunk(computation),
        CoreNode::Value(value) => value,
        CoreNode::ValueType(_) | CoreNode::CompType(_) => {
            panic!("a type is no definition's body")
        },
    };
    let from_arena = present_definition(
        &CoreSource::new(&arena, names).naming(constructors),
        CoreNode::Value(body),
        page,
        Form::Explicit.into(),
    )
    .expect("the arena's body lays out");
    let item = |position: usize, key: &str, body| {
        Item::new(
            ItemKey::from(key),
            Declaration::new(
                ConstantIndex::from(position),
                Maybe::Absent(signature::Absent::Unsigned),
                body,
                OriginToken::from(position),
            ),
        )
    };
    let items = names
        .iter()
        .enumerate()
        .map(|(position, name)| item(position, name.as_ref(), Maybe::Absent(body::Absent::Hole)))
        .chain([item(names.len(), "it", Maybe::Present(body))])
        .collect();
    let mut program = Program::new(arena, items).expect("the items ascend");
    let checked = check_program(&mut program, CheckBudget::DEFAULT).expect("the order builds");
    let content = checked
        .checkpoints()
        .items()
        .last()
        .expect("one checkpoint per item")
        .content();
    let DeclarationRoots::Value {
        body: Maybe::Present(projected),
        ..
    } = *content.declaration()
    else {
        panic!("the item's content holds its body");
    };
    let nodes = content.debruijn(projected).expect("a closed body projects");
    let from_content = present_definition(
        &ContentSource::from(nodes.as_slice()).naming(constructors),
        NodeIndex::from(0_usize),
        page,
        Form::Explicit.into(),
    )
    .expect("the content's body lays out");
    assert_eq!(
        (from_content.as_ref(), from_content.fidelity()),
        (from_arena.as_ref(), from_arena.fidelity()),
        "the content table spells the arena's body"
    );
}

/// The integer literal `digits`, nonnegative.
///
/// # Specification
/// trivial.
fn integer(
    arena: &mut CoreArena,
    digits: Digits,
) -> ValueId
{
    arena.value_literal(Literal::Integer(IntegerLiteral::new(
        Sign::NonNegative,
        Magnitude::from_decimal_text(String::from(digits.0)).expect("decimal digits"),
    )))
}

/// Decimal digits a fixture writes.
#[derive(Clone, Copy)]
#[repr(transparent)]
struct Digits(&'static str);

/// The innermost bound value.
///
/// # Specification
/// trivial.
fn bound(arena: &mut CoreArena) -> ValueId
{
    arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32))
}

/// The thunk of the computation returning one.
///
/// # Specification
/// trivial.
fn returns_one(arena: &mut CoreArena) -> ValueId
{
    let one = integer(arena, Digits("1"));
    let returned = arena.computation_return(one);
    arena.value_thunk(returned)
}

/// Every term former the arena builds without a signature, from both
/// zones, as a closed body, by name.
///
/// # Specification
/// trivial.
fn corpus() -> Vec<(What, Body)>
{
    let unit: Body = |a| a.value_unit();
    Vec::from([
        (What("unit"), unit),
        (What("integer"), |a| integer(a, Digits("42"))),
        (What("string"), |a| {
            a.value_literal(Literal::Text(StringLiteral::new(String::from("two words"))))
        }),
        (What("pair"), |a| {
            let numbers = one_two(a);
            a.value_tuple(&numbers)
        }),
        (What("triple"), |a| {
            let unit = a.value_unit();
            let one = integer(a, Digits("1"));
            a.value_tuple(&[unit, one, unit])
        }),
        (What("injection"), |a| {
            let one = integer(a, Digits("1"));
            a.value_injection(Summand::from(1_usize), one)
        }),
        (What("record"), |a| {
            let (one, two) = (integer(a, Digits("1")), integer(a, Digits("2")));
            a.value_record(
                [("x", one), ("y", two)]
                    .map(|(label, field)| (FieldLabel::from(String::from(label)), field))
                    .into(),
            )
        }),
        (What("list"), |a| {
            let nil = a.value_list_nil();
            let one = integer(a, Digits("1"));
            a.value_list_cons(one, nil)
        }),
        (What("quoted type"), |a| {
            let integer_type = a.value_type_base(BaseType::Integer);
            let unit_type = a.value_type_unit();
            let product = a.value_type_product(&[integer_type, unit_type]);
            a.value_quote(product)
        }),
        (What("returned"), returns_one),
        (What("function"), |a| {
            let x = bound(a);
            let returned = a.computation_return(x);
            let function = a.computation_lambda(returned);
            a.value_thunk(function)
        }),
        (What("call"), |a| {
            let x = bound(a);
            let returned = a.computation_return(x);
            let function = a.computation_lambda(returned);
            let one = integer(a, Digits("1"));
            let called = a.computation_application(function, one);
            a.value_thunk(called)
        }),
        (What("bind"), |a| {
            let one = integer(a, Digits("1"));
            let bound_first = a.computation_return(one);
            let x = bound(a);
            let pair = a.value_tuple(&[x, x]);
            let rest = a.computation_return(pair);
            let sequenced = a.computation_bind(bound_first, rest);
            a.value_thunk(sequenced)
        }),
        (What("force"), |a| {
            let held = returns_one(a);
            let forced = a.computation_force(held);
            a.value_thunk(forced)
        }),
        (What("operator"), |a| {
            let add = PRELUDE
                .iter()
                .copied()
                .find(|primitive| <&'static str>::from(primitive.name()) == "add")
                .expect("the prelude adds");
            let numbers = one_two(a);
            let added = a.computation_primitive(add, Arguments::Binary(numbers));
            a.value_thunk(added)
        }),
        (What("case"), |a| {
            let unit = a.value_unit();
            let scrutinee = a.value_injection(Summand::from(0_usize), unit);
            let x = bound(a);
            let arms = [a.computation_return(x), a.computation_return(unit)];
            let cased = a.computation_case(scrutinee, &arms);
            a.value_thunk(cased)
        }),
        (What("split"), |a| {
            let numbers = one_two(a);
            let pair = a.value_tuple(&numbers);
            let x = bound(a);
            let rest = a.computation_return(x);
            let split = a.computation_split(pair, ComponentCount::from(2_usize), rest);
            a.value_thunk(split)
        }),
        (What("list case"), |a| {
            let nil = a.value_list_nil();
            let zero = integer(a, Digits("0"));
            let on_nil = a.computation_return(zero);
            let x = bound(a);
            let on_cons = a.computation_return(x);
            let cased = a.computation_list_case(nil, on_nil, on_cons);
            a.value_thunk(cased)
        }),
        (What("ascription"), |a| {
            let one = integer(a, Digits("1"));
            let returned = a.computation_return(one);
            let integer_type = a.value_type_base(BaseType::Integer);
            let ty = a.comp_type_returner(integer_type);
            let ascribed = a.computation_ascribe(returned, ty);
            a.value_thunk(ascribed)
        }),
        (What("lazy pair"), |a| {
            let [one, two] = one_two(a);
            let returns = [a.computation_return(one), a.computation_return(two)];
            let lazy = a.computation_with(&returns);
            let projected = a.computation_project(gandr_core_term::Component::from(1_usize), lazy);
            a.value_thunk(projected)
        }),
        (What("reset"), |a| {
            let one = integer(a, Digits("1"));
            let returned = a.computation_return(one);
            let reset = a.computation_reset(returned);
            a.value_thunk(reset)
        }),
        (What("static application"), |a| {
            let x = bound(a);
            let operator = a.value_static_lambda(x);
            let one = integer(a, Digits("1"));
            a.value_static_application(operator, one)
        }),
        (What("perform"), |a| {
            let signature = proc(a);
            let unit = a.value_unit();
            let performed = a.computation_perform(signature, "exit".into(), unit);
            a.value_thunk(performed)
        }),
        (What("handle"), |a| {
            let signature = proc(a);
            let unit = a.value_unit();
            let subject = a.computation_perform(signature.clone(), "exit".into(), unit);
            let answer = bound(a);
            let on_return = a.computation_return(answer);
            let replied = a.computation_return(unit);
            let continuation = bound(a);
            let body = a.computation_resume(continuation, replied);
            let handled = a.computation_handle(
                signature,
                subject,
                on_return,
                Arc::from([EffectClause {
                    operation: "exit".into(),
                    body,
                }]),
            );
            a.value_thunk(handled)
        }),
        (What("abandon"), |a| {
            let stack = a.value_reify(Arc::from([]));
            let abandoned = a.computation_abandon(stack);
            a.value_thunk(abandoned)
        }),
        (What("reified stack"), |a| {
            let unit = a.value_unit();
            let rest = a.computation_return(unit);
            a.value_reify(Arc::from([StackFrame::Apply(unit), StackFrame::Bind(rest)]))
        }),
        (What("transport"), |a| {
            let unit_type = a.value_type_unit();
            let code = a.value_quote(unit_type);
            let path = a.value_here(code);
            let unit = a.value_unit();
            let moved = a.computation_transport(path, unit);
            a.value_thunk(moved)
        }),
        (What("telescope transport"), |a| {
            let unit_type = a.value_type_unit();
            let motive = a.comp_type_returner(unit_type);
            let code = a.value_quote(unit_type);
            let path = a.value_here(code);
            let unit = a.value_unit();
            let moved = a.computation_telescope_transport(motive, path, unit, unit, unit);
            a.value_thunk(moved)
        }),
        (What("tuple projection"), |a| {
            let numbers = one_two(a);
            let pair = a.value_tuple(&numbers);
            let projected =
                a.computation_tuple_projection(pair, gandr_kernel_term::Component::from(1_usize));
            a.value_thunk(projected)
        }),
        (What("list fold"), |a| {
            let unit_type = a.value_type_unit();
            let nil = a.value_list_nil();
            let unit = a.value_unit();
            let on_nil = a.computation_return(unit);
            let x = bound(a);
            let on_cons = a.computation_return(x);
            let folded = a.computation_list_fold(unit_type, unit_type, nil, on_nil, on_cons);
            a.value_thunk(folded)
        }),
        (What("send"), |a| {
            let unit = a.value_unit();
            let parent = a.computation_session(SessionAction::Send {
                endpoint: DeBruijnIndex::from(0_u32),
                payload: unit,
            });
            forked(a, parent)
        }),
        (What("select"), |a| {
            let parent = a.computation_session(SessionAction::Select {
                endpoint: DeBruijnIndex::from(0_u32),
                label: FieldLabel::from(String::from("next")),
            });
            forked(a, parent)
        }),
        (What("exclusive access"), |a| {
            let unit = a.value_unit();
            let unwind = a.computation_return(unit);
            let index = integer(a, Digits("0"));
            let resumed = a.computation_memory(MemoryForm::Resume {
                view: DeBruijnIndex::from(0_u32),
                value: unit,
            });
            let access = a.computation_memory(MemoryForm::Access {
                mode: AccessMode::Exclusive { unwind },
                held: DeBruijnIndex::from(0_u32),
                place: Place::At { index },
                body: resumed,
            });
            held(a, access)
        }),
        (What("shared access"), |a| {
            let aborted = a.computation_memory(MemoryForm::Abort {
                view: DeBruijnIndex::from(0_u32),
            });
            let access = a.computation_memory(MemoryForm::Access {
                mode: AccessMode::Shared,
                held: DeBruijnIndex::from(0_u32),
                place: Place::Whole,
                body: aborted,
            });
            held(a, access)
        }),
        (What("consume"), |a| {
            let consumed = a.computation_memory(MemoryForm::Consume {
                held: DeBruijnIndex::from(0_u32),
            });
            held(a, consumed)
        }),
        (What("session relation"), |a| {
            let ended = ended(a);
            let code = a.value_quote(ended);
            a.value_session_related(SessionRelation::Subtyping, code, code)
        }),
        (What("function flow"), |a| {
            let unit_type = a.value_type_unit();
            let code = a.value_quote(unit_type);
            let stay = a.value_stay(code);
            a.value_function_flow(stay, stay)
        }),
        (What("univalence"), |a| {
            let unit = a.value_unit();
            a.value_univalence(unit, unit)
        }),
        (What("lift"), |a| {
            let unit = a.value_unit();
            a.value_lift(Level::zero(), unit)
        }),
        (What("stack type"), |a| {
            let unit_type = a.value_type_unit();
            let returns = a.comp_type_returner(unit_type);
            let stack = a.value_type_stack(returns, returns);
            a.value_quote(stack)
        }),
        (What("buffer type"), |a| {
            let buffer = a.value_type_buffer();
            a.value_quote(buffer)
        }),
        (What("list type"), |a| {
            let unit_type = a.value_type_unit();
            let list = a.value_type_list(unit_type);
            a.value_quote(list)
        }),
        (What("universe"), |a| {
            let universe = a.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
            a.value_quote(universe)
        }),
        (What("element type"), |a| {
            let unit_type = a.value_type_unit();
            let code = a.value_quote(unit_type);
            let element = a.value_type_element(code, Level::zero());
            a.value_quote(element)
        }),
        (What("computation element"), |a| {
            let unit_type = a.value_type_unit();
            let returns = a.comp_type_returner(unit_type);
            let code = a.value_quote_computation(returns);
            let element = a.comp_type_element(code, Level::zero());
            a.value_quote_computation(element)
        }),
        (What("effectful returner"), |a| {
            let signature = proc(a);
            let unit_type = a.value_type_unit();
            let returns =
                a.comp_type_returner_with_effects(unit_type, EffectRow::singleton(signature));
            a.value_quote_computation(returns)
        }),
        (What("dependent function type"), |a| {
            let unit_type = a.value_type_unit();
            let returns = a.comp_type_returner(unit_type);
            let pi = a.comp_type_pi(unit_type, returns);
            a.value_quote_computation(pi)
        }),
        (What("static function type"), |a| {
            let universe = a.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
            let pi = a.value_type_static_pi(universe, universe);
            a.value_quote(pi)
        }),
        (What("dependent pair type"), |a| {
            let unit_type = a.value_type_unit();
            let sigma = a.value_type_sigma(unit_type, unit_type);
            a.value_quote(sigma)
        }),
        (What("flow type"), |a| {
            let unit_type = a.value_type_unit();
            let unit = a.value_unit();
            let flow = a.value_type_flow(unit_type, unit, unit);
            a.value_quote(flow)
        }),
        (What("session type with a payload"), |a| {
            let send = Protocol::new(
                Vec::from([
                    ProtocolSyntax::Send {
                        payload: PayloadSlot::from(0_usize),
                        next: ProtocolState::from(1_usize),
                    },
                    ProtocolSyntax::End,
                ]),
                ProtocolState::from(0_usize),
                PayloadCount::from(1_usize),
            )
            .expect("a send, then the end");
            let payload = a.value_type_unit();
            let session = SessionType::new(Arc::new(send), Arc::from([payload]))
                .expect("one payload for one slot");
            let ty = a.value_type_session(session);
            a.value_quote(ty)
        }),
        (What("nested"), |a| {
            let unit = a.value_unit();
            let returned = a.computation_return(unit);
            a.value_nested(returned)
        }),
        (What("dependent split"), |a| {
            let numbers = one_two(a);
            let pair = a.value_tuple(&numbers);
            let unit_type = a.value_type_unit();
            let motive = a.comp_type_returner(unit_type);
            let x = bound(a);
            let rest = a.computation_return(x);
            let split =
                a.computation_dependent_split(pair, ComponentCount::from(2_usize), motive, rest);
            a.value_thunk(split)
        }),
        (What("hole"), |a| a.value_hole(HoleId::from(0_u32))),
    ])
}

/// The integer literals one and two, in order.
///
/// # Specification
/// trivial.
fn one_two(arena: &mut CoreArena) -> [ValueId; 2]
{
    [integer(arena, Digits("1")), integer(arena, Digits("2"))]
}

/// The one-operation interface `Proc`, its `exit` taking and answering the
/// unit.
///
/// # Specification
/// trivial.
fn proc(arena: &mut CoreArena) -> EffectSig
{
    let unit = arena.value_type_unit();
    EffectSig::new(EffectName::from("Proc"), [EffectOp {
        name: "exit".into(),
        payload: unit,
        reply: unit,
    }])
    .expect("one operation is a signature")
}

/// The session type that has ended.
///
/// # Specification
/// trivial.
fn ended(arena: &mut CoreArena) -> ValueTypeId
{
    let protocol = Protocol::new(
        Vec::from([ProtocolSyntax::End]),
        ProtocolState::from(0_usize),
        PayloadCount::default(),
    )
    .expect("the end is a protocol");
    arena.value_type_session(
        SessionType::new(Arc::new(protocol), Arc::from([])).expect("no payloads"),
    )
}

/// A fork whose child returns the unit and whose parent is `parent`, over the
/// ended session, thunked.
///
/// # Specification
/// trivial.
fn forked(
    arena: &mut CoreArena,
    parent: ComputationId,
) -> ValueId
{
    let protocol = ended(arena);
    let unit = arena.value_unit();
    let child = arena.computation_return(unit);
    let fork = arena.computation_session(SessionAction::Fork {
        protocol,
        child,
        parent,
    });
    arena.value_thunk(fork)
}

/// The unit held as many, `body` its scope, thunked.
///
/// # Specification
/// trivial.
fn held(
    arena: &mut CoreArena,
    body: ComputationId,
) -> ValueId
{
    let unit = arena.value_unit();
    let hold = arena.computation_memory(MemoryForm::Hold {
        value: unit,
        body,
        grade: HoldGrade::Many,
    });
    arena.value_thunk(hold)
}

/// Every term former of the corpus spells the same, at the same fidelity,
/// whether the printer reads it from the arena or from the content table
/// the incremental checker projects.
#[test]
fn every_term_former_spells_from_its_content_as_from_its_arena()
{
    for (what, body) in corpus() {
        let mut arena = CoreArena::new();
        let root = body(&mut arena);
        println!("{}", what.0);
        agrees(&arena, &[], CoreNode::Value(root));
    }
}
