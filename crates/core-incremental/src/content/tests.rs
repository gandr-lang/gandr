use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_checker::Declaration;
use gandr_core_checker::OriginToken;
use gandr_core_checker::body;
use gandr_core_checker::signature;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Sign;
use quenchant_shape::shape::Maybe;

use super::ContentNode;
use super::Opacity;
use super::Sort;
use super::TypeContent;
use super::encode_item;
use super::seating;
use crate::boundary::ItemOrdinal;
use crate::boundary::NodeIndex;
use crate::boundary::Occurrence;
use crate::region::Item;
use crate::region::ItemKey;
use crate::region::Program;
use crate::region::Reference;

/// The program of one item `it` at position 0 with `signature` and `body`.
///
/// # Specification
/// - requires: nothing; unresolved ids are allowed.
/// - ensures: one item at position zero with the supplied two roots.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — independent allocation, sharing and an unresolved body
///   exercise the roots through item encoding.
/// - witness: `content::tests::content_is_free_of_arena_ids`
/// - witness: `content::tests::a_shared_node_is_listed_once`
/// - witness: `content::tests::an_unresolved_id_makes_the_item_opaque`
#[spec(ensures: |ret| ret.items().len() == 1
        && ret.items().first().is_some_and(|item| matches!(item.declaration().content(), gandr_core_checker::DeclarationContent::Value { signature: held_signature, body: held_body } if *held_signature == signature && *held_body == body)
            && item.declaration().constant() == ConstantIndex::from(0_usize)))]
fn single(
    arena: CoreArena,
    signature: Maybe<ValueTypeId, signature::Absent>,
    body: Maybe<ValueId, body::Absent>,
) -> Program
{
    Program::new(arena, vec![Item::new(
        ItemKey::from("it"),
        Declaration::new(
            ConstantIndex::from(0_usize),
            signature,
            body,
            OriginToken::from(0_usize),
        ),
    )])
    .expect("one item ascends")
}

#[test]
fn control_graphs_preserve_scopes_and_signature_edges()
{
    use gandr_core_term::Zone;
    use gandr_core_term::control::EffectClause;
    use gandr_core_term::control::StackFrame;
    use gandr_core_term::effect::EffectOp;
    use gandr_core_term::effect::EffectRow;
    use gandr_core_term::effect::EffectSig;
    use gandr_kernel_term::Side;
    let build = |noise: usize, reply, bound: u32, operation: &str| {
        let mut arena = CoreArena::new();
        for _ in 0 .. noise {
            let _ = arena.value_unit();
            let _ = arena.value_type_unit();
        }
        let unit = arena.value_unit();
        let variable = arena.value_variable(Zone::Intuitionistic, bound.into());
        let unit_type = arena.value_type_unit();
        let reply_type = arena.value_type_base(reply);
        let signature = EffectSig::new("State".into(), [EffectOp {
            name: operation.into(),
            payload: unit_type,
            reply: reply_type,
        }])
        .expect("one operation");
        let input = arena
            .comp_type_returner_with_effects(unit_type, EffectRow::singleton(signature.clone()));
        let output = arena.comp_type_returner(reply_type);
        let output = arena.comp_type_with(input, output);
        let ty = arena.value_type_stack(input, output);
        let returned = arena.computation_return(variable);
        let performed = arena.computation_perform(signature.clone(), operation.into(), unit);
        let resumed = arena.computation_resume(variable, performed);
        let shifted = arena.computation_shift(resumed);
        let reset = arena.computation_reset(shifted);
        let pair = arena.computation_with(reset, returned);
        let projected = arena.computation_project(Side::Right, pair);
        let handled = arena.computation_handle(
            signature,
            projected,
            returned,
            alloc::sync::Arc::from([EffectClause {
                operation: operation.into(),
                body: returned,
            }]),
        );
        let literal = arena.value_reify(alloc::sync::Arc::from([
            StackFrame::Apply(unit),
            StackFrame::Bind(handled),
            StackFrame::Project(Side::Left),
        ]));
        (
            single(arena, Maybe::Present(ty), Maybe::Present(literal)),
            ty,
        )
    };
    let (source, ty) = build(0, BaseType::Integer, 0, "get");
    let original = encode_item(source.arena(), source.layout(), ItemOrdinal::from(0_usize)).content;
    let (renumbered, _) = build(7, BaseType::Integer, 0, "get");
    assert_eq!(
        original,
        encode_item(
            renumbered.arena(),
            renumbered.layout(),
            ItemOrdinal::from(0_usize)
        )
        .content
    );
    for (changed, _) in [
        build(0, BaseType::String, 0, "get"),
        build(0, BaseType::Integer, 1, "get"),
        build(0, BaseType::Integer, 0, "put"),
    ] {
        assert_ne!(
            original,
            encode_item(
                changed.arena(),
                changed.layout(),
                ItemOrdinal::from(0_usize)
            )
            .content,
            "operation types, binder indices, and names contribute to identity"
        );
    }
    assert!(
        !original
            .nodes()
            .iter()
            .any(|node| matches!(node, ContentNode::Unresolved(_)))
    );
    let content = TypeContent::of_value_type(&source, ty);
    let mut target = CoreArena::new();
    let _ = target.value_type_base(BaseType::String);
    let mut target = single(
        target,
        Maybe::Absent(signature::Absent::Unsigned),
        Maybe::Absent(body::Absent::Hole),
    );
    let (arena, layout) = target.parts_mut();
    let Maybe::Present(minted) = content.mint(arena, layout)
    else {
        panic!("closed Stack/With codes seat");
    };
    assert_eq!(TypeContent::of_value_type(&target, minted), content);
}

#[test]
fn capability_graphs_keep_authority_region_and_scope()
{
    use gandr_core_term::Zone;
    use gandr_core_term::control::EffectClause;
    use gandr_core_term::effect::EffectOp;
    use gandr_core_term::effect::EffectRow;
    use gandr_core_term::effect::EffectSig;
    use gandr_core_term::effect::capability::CapabilityGrade;
    use gandr_core_term::effect::capability::Region;
    use gandr_core_term::effect::capability::RegionDepth;
    /// The one variation each build makes.
    #[derive(Clone, Copy)]
    enum Variation
    {
        /// The graph as written.
        Base,
        /// The capability scoped rather than held.
        Scoped,
        /// The capability consumable rather than durable.
        Consumable,
        /// The authority granting the other operation.
        Authority,
        /// A deep handler in place of the scope.
        Handler,
    }
    let build = |noise: usize, variation: Variation| {
        let mut arena = CoreArena::new();
        for _ in 0 .. noise {
            let _ = arena.value_unit();
            let _ = arena.value_type_unit();
        }
        let unit = arena.value_unit();
        let variable = arena.value_variable(Zone::Intuitionistic, 0_u32.into());
        let unit_type = arena.value_type_unit();
        let reply = arena.value_type_base(BaseType::Integer);
        let signature = EffectSig::new("State".into(), [
            EffectOp {
                name: "get".into(),
                payload: unit_type,
                reply,
            },
            EffectOp {
                name: "put".into(),
                payload: reply,
                reply: unit_type,
            },
        ])
        .expect("two operations");
        let granted = if matches!(variation, Variation::Authority) {
            "put"
        }
        else {
            "get"
        };
        let authority =
            EffectRow::authority(&[signature.restrict([&granted.into()]).expect("granted")])
                .expect("one restriction");
        let region = if matches!(variation, Variation::Scoped) {
            Region::Scoped(RegionDepth::from(1_u32))
        }
        else {
            Region::Held
        };
        let grade = if matches!(variation, Variation::Consumable) {
            CapabilityGrade::Consumable
        }
        else {
            CapabilityGrade::Durable
        };
        let capability = arena.value_type_capability(authority, grade, region);
        let answer =
            arena.comp_type_returner_with_effects(reply, EffectRow::singleton(signature.clone()));
        let arrow = arena.comp_type_arrow(capability, answer);
        let ty = arena.value_type_thunk(arrow);
        let exercised = arena.computation_exercise(variable, signature.clone(), "get".into(), unit);
        let returned = arena.computation_return(variable);
        let clauses = alloc::sync::Arc::from([
            EffectClause {
                operation: "get".into(),
                body: returned,
            },
            EffectClause {
                operation: "put".into(),
                body: returned,
            },
        ]);
        let scoped = if matches!(variation, Variation::Handler) {
            arena.computation_handle(signature, exercised, returned, clauses)
        }
        else {
            arena.computation_scope(signature, exercised, returned, clauses)
        };
        let body = arena.computation_bind(exercised, scoped);
        let lambda = arena.computation_lambda(body);
        let thunk = arena.value_thunk(lambda);
        (single(arena, Maybe::Present(ty), Maybe::Present(thunk)), ty)
    };
    let content = |program: &Program| {
        encode_item(
            program.arena(),
            program.layout(),
            ItemOrdinal::from(0_usize),
        )
        .content
    };
    let (source, ty) = build(0, Variation::Base);
    let original = content(&source);
    assert_eq!(
        original,
        content(&build(5, Variation::Base).0),
        "identity reads content, never ids"
    );
    for variation in [
        Variation::Scoped,
        Variation::Consumable,
        Variation::Authority,
        Variation::Handler,
    ] {
        assert_ne!(
            original,
            content(&build(0, variation).0),
            "region, grade, authority and the scope each contribute to identity"
        );
    }
    let table = TypeContent::of_value_type(&source, ty);
    let mut target = single(
        CoreArena::new(),
        Maybe::Absent(signature::Absent::Unsigned),
        Maybe::Absent(body::Absent::Hole),
    );
    let (arena, layout) = target.parts_mut();
    let Maybe::Present(minted) = table.mint(arena, layout)
    else {
        panic!("a capability type seats");
    };
    assert_eq!(TypeContent::of_value_type(&target, minted), table);
}

/// The integer literal zero.
///
/// # Specification
/// trivial.
fn zero() -> Literal
{
    Literal::Integer(IntegerLiteral::new(Sign::NonNegative, Magnitude::zero()))
}

/// `U (Integer → F Integer)`, its one `Integer` node shared by domain and
/// result, built in `arena`.
///
/// # Specification
/// - requires: the arena has identifier headroom for the four nodes.
/// - ensures: a thunk of an arrow whose integer domain is also its result.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — content has four entries despite two integer uses, and
///   reconstruction in a noisy arena preserves that shared graph.
/// - witness: `content::tests::a_type_minted_back_has_its_own_content`
/// - witness: `content::tests::a_signature_renumbers_to_its_own_type_content`
#[spec(ensures: |ret| match arena.value_type(ret) {
            | Some(&gandr_core_term::ValueType::Thunk(arrow)) => match arena.comp_type(arrow) {
                | Some(&gandr_core_term::CompType::Arrow { domain, codomain }) => {
                    arena.value_type(domain)
                        == Some(&gandr_core_term::ValueType::Base(BaseType::Integer))
                        && arena.comp_type(codomain)
                            == Some(&gandr_core_term::CompType::Returner { result: domain, effects: gandr_core_term::effect::EffectRow::EMPTY })
                },
                | _ => false,
            },
            | _ => false,
        })]
fn shared_arrow(arena: &mut CoreArena) -> ValueTypeId
{
    let integer = arena.value_type_base(BaseType::Integer);
    let returner = arena.comp_type_returner(integer);
    let arrow = arena.comp_type_arrow(integer, returner);
    arena.value_type_thunk(arrow)
}

#[test]
fn a_type_minted_back_has_its_own_content()
{
    let mut source = CoreArena::new();
    let ty = shared_arrow(&mut source);
    let program = single(
        source,
        Maybe::Present(ty),
        Maybe::Absent(body::Absent::Hole),
    );
    let content = TypeContent::of_value_type(&program, ty);
    assert_eq!(
        content.nodes().len(),
        4_usize,
        "thunk, arrow, the shared integer once, returner"
    );
    let mut target = CoreArena::new();
    // Unrelated nodes first, so the minted ids differ from the source's.
    let _noise = target.value_type_unit();
    let _noise = target.value_type_base(BaseType::String);
    let mut minted_into = single(
        target,
        Maybe::Absent(signature::Absent::Unsigned),
        Maybe::Absent(body::Absent::Hole),
    );
    let minted = {
        let (arena, layout) = minted_into.parts_mut();
        content.mint(arena, layout)
    };
    let Maybe::Present(minted) = minted
    else {
        panic!("a type table of admitted formers seats: {minted:?}");
    };
    assert_eq!(
        TypeContent::of_value_type(&minted_into, minted),
        content,
        "the minted type reads back as the table it came from, sharing and all"
    );
}

#[test]
fn every_dependent_former_mints_back_as_its_own_table()
{
    let mut source = CoreArena::new();
    let integer = source.value_type_base(BaseType::Integer);
    let string = source.value_type_base(BaseType::String);
    let sigma = source.value_type_sigma(integer, string);
    let static_pi = source.value_type_static_pi(string, integer);
    let returner = source.comp_type_returner(integer);
    let pi = source.comp_type_pi(string, returner);
    let thunk = source.value_type_thunk(pi);
    let ty = source.value_type_product(&[sigma, static_pi, thunk]);
    let program = single(
        source,
        Maybe::Present(ty),
        Maybe::Absent(body::Absent::Hole),
    );
    let content = TypeContent::of_value_type(&program, ty);
    let mut target = CoreArena::new();
    let _noise = target.value_type_unit();
    let mut minted_into = single(
        target,
        Maybe::Absent(signature::Absent::Unsigned),
        Maybe::Absent(body::Absent::Hole),
    );
    let minted = {
        let (arena, layout) = minted_into.parts_mut();
        content.mint(arena, layout)
    };
    let Maybe::Present(minted) = minted
    else {
        panic!("a sigma, a static pi and a pi seat: {minted:?}");
    };
    assert_eq!(TypeContent::of_value_type(&minted_into, minted), content);
}

#[test]
fn a_data_type_mints_only_unapplied()
{
    let it = || Reference::Item {
        key: ItemKey::from("it"),
        occurrence: Occurrence::from(0_usize),
    };
    let mut program = single(
        CoreArena::new(),
        Maybe::Absent(signature::Absent::Unsigned),
        Maybe::Absent(body::Absent::Hole),
    );
    let (arena, layout) = program.parts_mut();
    let bare = TypeContent::from_nodes(vec![ContentNode::Data {
        declaration: it(),
        arguments: Vec::new(),
    }]);
    assert!(
        matches!(bare.mint(arena, layout), Maybe::Present(_)),
        "a data type of no arguments seats at its declaration"
    );
    let applied = TypeContent::from_nodes(vec![
        ContentNode::Data {
            declaration: it(),
            arguments: vec![NodeIndex::from(1_usize)],
        },
        ContentNode::Constant(Reference::Unoccupied),
    ]);
    assert_eq!(
        applied.mint(arena, layout),
        Maybe::Absent(seating::Absent::Unseatable),
        "and one applied to an argument does not"
    );
}

#[test]
fn renumbering_carries_every_frame_and_clause_body_to_its_image()
{
    use alloc::sync::Arc;

    use gandr_core_term::control::EffectClause;
    use gandr_core_term::control::StackFrame;
    use gandr_core_term::effect::EffectName;
    use gandr_core_term::effect::EffectOp;
    use gandr_core_term::effect::EffectSig;
    use gandr_core_term::effect::OperationName;
    use gandr_kernel_term::Side;

    let index = NodeIndex::from;
    let mut shifted = |child: NodeIndex| NodeIndex::from(usize::from(child).saturating_add(10));
    let reify = |[apply, bind]: [usize; 2]| {
        ContentNode::Reify(Arc::from([
            StackFrame::Apply(index(apply)),
            StackFrame::Bind(index(bind)),
            StackFrame::Project(Side::Left),
        ]))
    };
    assert_eq!(
        super::map_children(&reify([1, 2]), &mut shifted),
        reify([11, 12])
    );
    let handle = |[subject, on_return, payload, body]: [usize; 4]| {
        let signature = EffectSig::new(EffectName::from("Probe"), [EffectOp {
            name: OperationName::from("ask"),
            payload: index(payload),
            reply: index(payload),
        }])
        .expect("one operation");
        ContentNode::Handle {
            signature,
            subject: index(subject),
            on_return: index(on_return),
            clauses: Arc::from([EffectClause {
                operation: OperationName::from("ask"),
                body: index(body),
            }]),
        }
    };
    assert_eq!(
        super::map_children(&handle([1, 2, 3, 4]), &mut shifted),
        handle([11, 12, 13, 14])
    );
}

#[test]
fn effect_rows_round_trip_without_losing_operation_types()
{
    use gandr_core_term::effect::EffectName;
    use gandr_core_term::effect::EffectOp;
    use gandr_core_term::effect::EffectRow;
    use gandr_core_term::effect::EffectSig;
    use gandr_core_term::effect::OperationName;
    let mut arena = CoreArena::new();
    let unit = arena.value_type_unit();
    let string = arena.value_type_base(BaseType::String);
    let list = arena.value_type_list(string);
    let integer = arena.value_type_base(BaseType::Integer);
    let io = EffectSig::new(EffectName::from("IO"), [EffectOp {
        name: OperationName::from("emit"),
        payload: string,
        reply: unit,
    }])
    .expect("distinct operations");
    let state = EffectSig::new(EffectName::from("State"), [
        EffectOp {
            name: OperationName::from("put"),
            payload: list,
            reply: integer,
        },
        EffectOp {
            name: OperationName::from("get"),
            payload: unit,
            reply: list,
        },
    ])
    .expect("distinct operations");
    let effects = EffectRow::from_signatures([state, io]).expect("distinct interfaces");
    let returner = arena.comp_type_returner_with_effects(unit, effects);
    let root = arena.value_type_thunk(returner);
    let source = Program::new(arena, Vec::new()).expect("empty declaration order");
    let content = TypeContent::of_value_type(&source, root);
    let Some(&ContentNode::Returner {
        result,
        ref effects,
    }) = content.nodes().get(1)
    else {
        panic!("thunk's returner");
    };
    assert_eq!(result, NodeIndex::from(2_usize));
    assert_eq!(
        effects
            .signatures()
            .map(|signature| signature.name().as_ref())
            .collect::<Vec<_>>(),
        ["IO", "State"]
    );
    assert_eq!(
        effects
            .signatures()
            .flat_map(|signature| signature
                .operations()
                .map(|operation| operation.name.as_ref()))
            .collect::<Vec<_>>(),
        ["emit", "get", "put"]
    );
    assert_eq!(effects.types().map(usize::from).collect::<Vec<_>>(), [
        3, 2, 2, 4, 4, 5
    ]);
    assert_eq!(
        content.nodes().get(2 ..),
        Some(
            [
                ContentNode::Product(Vec::new()),
                ContentNode::Base(BaseType::String),
                ContentNode::List(NodeIndex::from(3_usize)),
                ContentNode::Base(BaseType::Integer)
            ]
            .as_slice()
        )
    );
    let mut target = CoreArena::new();
    for _ in 0_u32 .. 7_u32 {
        let _noise = target.value_type_unit();
    }
    let mut target = Program::new(target, Vec::new()).expect("empty declaration order");
    let (arena, layout) = target.parts_mut();
    let Maybe::Present(minted) = content.mint(arena, layout)
    else {
        panic!("portable row types seat");
    };
    assert_ne!(minted, root);
    assert_eq!(TypeContent::of_value_type(&target, minted), content);
}

#[test]
fn an_unmintable_table_is_refused_by_name()
{
    let level = Level::zero();
    let cases = [
        (
            vec![
                ContentNode::PathUniverse(NodeIndex::from(1_usize), NodeIndex::from(1_usize)),
                ContentNode::Product(Vec::new()),
            ],
            seating::Absent::Unseatable,
        ),
        (
            vec![ContentNode::Product(vec![
                NodeIndex::from(0_usize),
                NodeIndex::from(0_usize),
            ])],
            seating::Absent::Cyclic,
        ),
        (
            vec![ContentNode::Unresolved(Sort::ValueType)],
            seating::Absent::Unresolved,
        ),
        (
            vec![ContentNode::Abstract(Reference::Item {
                key: ItemKey::from("elsewhere"),
                occurrence: Occurrence::from(0_usize),
            })],
            seating::Absent::Unplaced,
        ),
        (
            vec![
                ContentNode::Returner {
                    result: NodeIndex::from(1_usize),
                    effects: gandr_core_term::effect::EffectRow::EMPTY,
                },
                ContentNode::Base(BaseType::Integer),
            ],
            seating::Absent::IllSorted,
        ),
        (
            vec![
                ContentNode::Element {
                    code: NodeIndex::from(1_usize),
                    target: level,
                },
                ContentNode::Constant(Reference::Unoccupied),
            ],
            seating::Absent::Unseatable,
        ),
    ];
    for (nodes, expected) in cases {
        let mut program = single(
            CoreArena::new(),
            Maybe::Absent(signature::Absent::Unsigned),
            Maybe::Absent(body::Absent::Hole),
        );
        let (arena, layout) = program.parts_mut();
        assert_eq!(
            TypeContent::from_nodes(nodes).mint(arena, layout),
            Maybe::Absent(expected),
            "each unmintable table names its reason"
        );
    }
}

#[test]
fn content_is_free_of_arena_ids()
{
    let build = |noise: usize| {
        let mut arena = CoreArena::new();
        for _ in 0 .. noise {
            let _unused = arena.value_unit();
            let _unused = arena.value_type_unit();
        }
        let ty = arena.value_type_base(BaseType::Integer);
        let literal = arena.value_literal(zero());
        let program = single(arena, Maybe::Present(ty), Maybe::Present(literal));
        encode_item(
            program.arena(),
            program.layout(),
            ItemOrdinal::from(0_usize),
        )
        .content
    };
    let plain = build(0_usize);
    assert_eq!(plain, build(5_usize), "ids differ, content does not");
    assert_eq!(
        plain.nodes(),
        [
            ContentNode::Base(BaseType::Integer),
            ContentNode::Literal(zero())
        ],
        "the signature root first, then the body's"
    );
    assert_eq!(
        plain.reference(),
        &Reference::Item {
            key: ItemKey::from("it"),
            occurrence: Occurrence::from(0_usize),
        },
        "the item is named by key and occurrence, not by position"
    );
}

#[test]
fn a_shared_node_is_listed_once()
{
    let mut shared = CoreArena::new();
    let literal = shared.value_literal(zero());
    let pair = shared.value_tuple(&[literal, literal]);
    let shared = single(
        shared,
        Maybe::Absent(signature::Absent::Unsigned),
        Maybe::Present(pair),
    );
    let shared = encode_item(shared.arena(), shared.layout(), ItemOrdinal::from(0_usize)).content;
    assert_eq!(
        shared.nodes(),
        [
            ContentNode::Tuple(vec![NodeIndex::from(1_usize), NodeIndex::from(1_usize)]),
            ContentNode::Literal(zero()),
        ],
        "one entry for the shared literal"
    );
    let mut apart = CoreArena::new();
    let first = apart.value_literal(zero());
    let second = apart.value_literal(zero());
    let pair = apart.value_tuple(&[first, second]);
    let apart = single(
        apart,
        Maybe::Absent(signature::Absent::Unsigned),
        Maybe::Present(pair),
    );
    let apart = encode_item(apart.arena(), apart.layout(), ItemOrdinal::from(0_usize)).content;
    assert_eq!(apart.nodes().len(), 3_usize, "two literals, two entries");
    assert_ne!(shared, apart, "sharing is part of the content");
}

#[test]
fn an_unresolved_id_makes_the_item_opaque()
{
    let mut larger = CoreArena::new();
    let _first = larger.value_unit();
    let foreign = larger.value_unit();
    let program = single(
        CoreArena::new(),
        Maybe::Absent(signature::Absent::Unsigned),
        Maybe::Present(foreign),
    );
    let content = encode_item(
        program.arena(),
        program.layout(),
        ItemOrdinal::from(0_usize),
    )
    .content;
    assert_eq!(
        content.nodes(),
        [ContentNode::Unresolved(Sort::Value)],
        "the id is listed by its sort"
    );
    assert_eq!(content.opacity(), Opacity::Opaque, "and the item is opaque");
}

#[test]
fn an_item_of_a_located_program_is_opaque()
{
    let item = |arena: &mut CoreArena, position: usize| {
        let integer = arena.value_type_base(BaseType::Integer);
        let zero = arena.value_literal(Literal::Integer(IntegerLiteral::new(
            Sign::NonNegative,
            Magnitude::zero(),
        )));
        Item::new(
            ItemKey::from("plain"),
            Declaration::new(
                ConstantIndex::from(position),
                Maybe::Present(integer),
                Maybe::Present(zero),
                OriginToken::from(position),
            ),
        )
    };
    let mut arena = CoreArena::new();
    let alone = vec![item(&mut arena, 0)];
    let alone = Program::new(arena, alone).expect("one item ascends");
    let alone = encode_item(alone.arena(), alone.layout(), ItemOrdinal::from(0_usize)).content;
    let mut arena = CoreArena::new();
    let beside = vec![
        Item::new(
            ItemKey::from("seat"),
            Declaration::world(ConstantIndex::from(0_usize), OriginToken::from(0_usize)),
        ),
        item(&mut arena, 1),
    ];
    let beside = Program::new(arena, beside).expect("two items ascend");
    let located = encode_item(beside.arena(), beside.layout(), ItemOrdinal::from(1_usize)).content;
    assert_eq!(
        (alone.opacity(), located.opacity()),
        (Opacity::Transparent, Opacity::Opaque),
        "the same item is transparent alone and opaque beside a world declaration"
    );
    assert_eq!(
        alone.nodes(),
        located.nodes(),
        "its nodes are the same; the program's locus is what differs"
    );
    let mut bytes = crate::codec::CheckpointBytes::default();
    assert_eq!(
        crate::codec::write_item_content(&mut bytes, &located),
        Err(crate::codec::CodecError::Unsupported(
            crate::codec::UnsupportedPersistence::Located
        )),
        "and it is refused persistence by name"
    );
}

#[test]
fn a_signature_renumbers_to_its_own_type_content()
{
    let mut arena = CoreArena::new();
    let ty = shared_arrow(&mut arena);
    let literal = arena.value_literal(zero());
    let returned = arena.computation_return(literal);
    let lambda = arena.computation_lambda(returned);
    let thunk = arena.value_thunk(lambda);
    let program = single(arena, Maybe::Present(ty), Maybe::Present(thunk));
    let content = encode_item(
        program.arena(),
        program.layout(),
        ItemOrdinal::from(0_usize),
    )
    .content;
    let interleaved: Vec<&ContentNode> = content.nodes().iter().collect();
    assert!(
        matches!(interleaved.get(1), Some(&&ContentNode::Thunk(_))),
        "the body's root is discovered before the signature's children"
    );
    assert_eq!(
        content.signature_type(),
        Some(TypeContent::of_value_type(&program, ty)),
        "the signature renumbered from its root is the type encoded alone"
    );
}

#[test]
fn renumbering_closes_dangling_and_cyclic_tables()
{
    let index = NodeIndex::from;
    let nodes = [
        ContentNode::Product(Vec::new()),
        ContentNode::Product(vec![index(3_usize), index(3_usize)]),
        ContentNode::Abstract(Reference::Unoccupied),
        ContentNode::ThunkType(index(4_usize)),
        ContentNode::Returner {
            result: index(1_usize),
            effects: gandr_core_term::effect::EffectRow::EMPTY,
        },
    ];
    assert_eq!(super::renumber(&nodes, index(1_usize)), [
        ContentNode::Product(vec![index(1_usize), index(1_usize)]),
        ContentNode::ThunkType(index(2_usize)),
        ContentNode::Returner {
            result: index(0_usize),
            effects: gandr_core_term::effect::EffectRow::EMPTY
        },
    ]);
    assert_eq!(super::renumber(&nodes, index(2_usize)), [
        ContentNode::Abstract(Reference::Unoccupied),
    ]);
    let dangling = [ContentNode::Case {
        scrutinee: index(usize::MAX),
        branches: vec![index(0_usize), index(usize::MAX)],
    }];
    assert_eq!(super::renumber(&dangling, index(0_usize)), [
        ContentNode::Case {
            scrutinee: index(1_usize),
            branches: vec![index(0_usize), index(1_usize)],
        },
        ContentNode::Unresolved(Sort::Value),
    ]);
    assert_eq!(super::renumber(&nodes, index(usize::MAX)), [
        ContentNode::Unresolved(Sort::Value),
    ]);
}

#[test]
fn malformed_type_tables_fail_by_structure()
{
    let index = NodeIndex::from;
    let cases = [
        vec![],
        vec![
            ContentNode::Product(vec![index(1_usize), index(usize::MAX)]),
            ContentNode::Product(Vec::new()),
        ],
        vec![
            ContentNode::Product(vec![index(1_usize), index(2_usize)]),
            ContentNode::Returner {
                result: index(2_usize),
                effects: gandr_core_term::effect::EffectRow::EMPTY,
            },
            ContentNode::Product(Vec::new()),
        ],
        vec![
            ContentNode::Arrow {
                domain: index(1_usize),
                codomain: index(1_usize),
            },
            ContentNode::Product(Vec::new()),
        ],
    ];
    for nodes in cases {
        let mut program = single(
            CoreArena::new(),
            Maybe::Absent(signature::Absent::Unsigned),
            Maybe::Absent(body::Absent::Hole),
        );
        let (arena, layout) = program.parts_mut();
        assert_eq!(
            TypeContent::from_nodes(nodes).mint(arena, layout),
            Maybe::Absent(seating::Absent::IllSorted)
        );
    }
}

#[test]
fn abstract_types_relocate_by_key_and_occurrence()
{
    let items = [17_usize, 42_usize]
        .into_iter()
        .map(|position| {
            Item::new(
                ItemKey::from("repeated"),
                Declaration::new(
                    ConstantIndex::from(position),
                    Maybe::Absent(signature::Absent::Unsigned),
                    Maybe::Absent(body::Absent::Hole),
                    OriginToken::from(position),
                ),
            )
        })
        .collect();
    let mut program = Program::new(CoreArena::new(), items).expect("ascending positions");
    let named = Reference::Item {
        key: ItemKey::from("repeated"),
        occurrence: Occurrence::from(1_usize),
    };
    let content = TypeContent::from_nodes(vec![ContentNode::Abstract(named)]);
    let minted = {
        let (arena, layout) = program.parts_mut();
        content.mint(arena, layout)
    };
    let Maybe::Present(id) = minted
    else {
        panic!("an existing occurrence must place: {minted:?}");
    };
    assert_eq!(
        program.arena().value_type(id),
        Some(&gandr_core_term::ValueType::Abstract(ConstantIndex::from(
            42_usize
        )))
    );
    assert_eq!(TypeContent::of_value_type(&program, id), content);
    let absent = TypeContent::from_nodes(vec![ContentNode::Abstract(Reference::Item {
        key: ItemKey::from("repeated"),
        occurrence: Occurrence::from(2_usize),
    })]);
    let (arena, layout) = program.parts_mut();
    assert_eq!(
        absent.mint(arena, layout),
        Maybe::Absent(seating::Absent::Unplaced)
    );
}
