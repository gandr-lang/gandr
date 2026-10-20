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

/// The formers of `nodes`, in table order.
///
/// # Specification
/// trivial.
fn formers(nodes: &[crate::support::SupportedNode]) -> Vec<ContentNode>
{
    nodes
        .iter()
        .map(crate::support::SupportedNode::former)
        .cloned()
        .collect()
}

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
fn an_operation_rule_is_content()
{
    use gandr_kernel_term::OperationNode;
    use gandr_kernel_term::OperationRule;
    use gandr_kernel_term::OperationRules;
    // `f(x) ==> x` and its twin `f(x) ==> f(x)`, `f` the item at position 0.
    let content = |right: &[OperationNode]| {
        let mut arena = CoreArena::new();
        let ty = arena.value_type_base(BaseType::Integer);
        let literal = arena.value_literal(Literal::Integer(IntegerLiteral::new(
            Sign::NonNegative,
            Magnitude::zero(),
        )));
        let call = OperationNode::Operation {
            constant: ConstantIndex::from(0_usize),
            arity: gandr_kernel_term::FieldCount::from(1_usize),
        };
        let x = OperationNode::Variable(gandr_kernel_term::RuleVariable::from(0_u32));
        let rules = OperationRules::new(vec![OperationRule::new([call, x].into(), right.into())]);
        let program = Program::new(arena, vec![Item::new(
            ItemKey::from("it"),
            Declaration::new(
                ConstantIndex::from(0_usize),
                Maybe::Present(ty),
                Maybe::Present(literal),
                OriginToken::from(0_usize),
            )
            .ruled(rules),
        )])
        .expect("one item ascends");
        encode_item(
            program.arena(),
            program.layout(),
            ItemOrdinal::from(0_usize),
        )
        .content
    };
    let x = OperationNode::Variable(gandr_kernel_term::RuleVariable::from(0_u32));
    let projection = content(&[x]);
    let super::DeclarationRoots::Value { ref rules, .. } = *projection.declaration()
    else {
        panic!("a ruled definition is a value");
    };
    let own = Reference::Item {
        key: ItemKey::from("it"),
        occurrence: Occurrence::from(0_usize),
    };
    assert_eq!(
        rules.first().and_then(|rule| rule.left.first()),
        Some(&super::RuleRoot::Operation {
            callee: own,
            arity: gandr_kernel_term::FieldCount::from(1_usize),
        }),
        "the operation's own call reads as the item's own reference"
    );
    let call = OperationNode::Operation {
        constant: ConstantIndex::from(0_usize),
        arity: gandr_kernel_term::FieldCount::from(1_usize),
    };
    assert_ne!(
        projection,
        content(&[call, x]),
        "a changed right side is changed content"
    );
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
    use gandr_kernel_term::Component;
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
        let output = arena.comp_type_with(&[input, output]);
        let ty = arena.value_type_stack(input, output);
        let returned = arena.computation_return(variable);
        let performed = arena.computation_perform(signature.clone(), operation.into(), unit);
        let resumed = arena.computation_resume(variable, performed);
        let shifted = arena.computation_shift(resumed);
        let reset = arena.computation_reset(shifted);
        let pair = arena.computation_with(&[reset, returned]);
        let projected = arena.computation_project(Component::from(1_usize), pair);
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
            StackFrame::Project(Component::from(0_usize)),
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
            .any(|node| matches!(*node.former(), ContentNode::Unresolved(_)))
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
    let bare = crate::fixture::type_content(&[ContentNode::Data {
        declaration: it(),
        arguments: Vec::new(),
    }]);
    assert!(
        matches!(bare.mint(arena, layout), Maybe::Present(_)),
        "a data type of no arguments seats at its declaration"
    );
    let applied = crate::fixture::type_content(&[
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
    use gandr_kernel_term::Component;

    let index = NodeIndex::from;
    let mut shifted = |child: NodeIndex| NodeIndex::from(usize::from(child).saturating_add(10));
    let reify = |[apply, bind]: [usize; 2]| {
        ContentNode::Reify(Arc::from([
            StackFrame::Apply(index(apply)),
            StackFrame::Bind(index(bind)),
            StackFrame::Project(Component::from(0_usize)),
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
    }) = content
        .nodes()
        .get(1)
        .map(crate::support::SupportedNode::former)
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
        content.nodes().get(2 ..).map(|nodes| nodes
            .iter()
            .map(crate::support::SupportedNode::former)
            .cloned()
            .collect::<Vec<_>>()),
        Some(vec![
            ContentNode::Product(Vec::new()),
            ContentNode::Base(BaseType::String),
            ContentNode::List(NodeIndex::from(3_usize)),
            ContentNode::Base(BaseType::Integer)
        ])
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
        // An open table is projected before it is minted, and refused alike.
        (
            vec![
                ContentNode::Element {
                    code: NodeIndex::from(1_usize),
                    target: Level::zero(),
                },
                ContentNode::Variable {
                    zone: gandr_core_term::Zone::Intuitionistic,
                    index: gandr_kernel_term::DeBruijnIndex::from(0_u32),
                },
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
            crate::fixture::type_content(&nodes).mint(arena, layout),
            Maybe::Absent(expected),
            "each unmintable table names its reason"
        );
    }
    let cyclic = [ContentNode::Product(vec![
        NodeIndex::from(0_usize),
        NodeIndex::from(0_usize),
    ])];
    let mut program = single(
        CoreArena::new(),
        Maybe::Absent(signature::Absent::Unsigned),
        Maybe::Absent(body::Absent::Hole),
    );
    let (arena, layout) = program.parts_mut();
    assert!(
        matches!(
            super::mint_table(&cyclic, arena, layout),
            Maybe::Absent(seating::Absent::Cyclic)
        ),
        "a de Bruijn table no arena can mint child before parent"
    );
    assert_eq!(
        crate::fixture::type_content(&cyclic).mint(arena, layout),
        Maybe::Absent(seating::Absent::Unresolved),
        "factoring closes the cycle with an unresolved leaf"
    );
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
        formers(plain.nodes()),
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
        formers(shared.nodes()),
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
    assert_eq!(
        shared, apart,
        "two equal literals are one entry: the arena's sharing is not content"
    );
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
        formers(content.nodes()),
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
    let interleaved: Vec<&ContentNode> = content
        .nodes()
        .iter()
        .map(crate::support::SupportedNode::former)
        .collect();
    assert!(
        matches!(interleaved.get(1), Some(&&ContentNode::Thunk(_))),
        "the body's root is discovered before the signature's children"
    );
    assert_eq!(
        content.signature_type(),
        Some(TypeContent::of_value_type(&program, ty)),
        "the signature renumbered from its root is the type encoded alone"
    );
    let signature = NodeIndex::from(0_usize);
    assert_eq!(
        content.debruijn(signature),
        TypeContent::of_value_type(&program, ty).debruijn(),
        "and its projection is the type's"
    );
}

#[test]
fn factoring_closes_dangling_and_cyclic_tables()
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
    assert_eq!(
        formers(TypeContent::tabulated(&nodes, index(1_usize)).nodes()),
        [
            ContentNode::Product(vec![index(1_usize), index(1_usize)]),
            ContentNode::ThunkType(index(2_usize)),
            ContentNode::Returner {
                result: index(3_usize),
                effects: gandr_core_term::effect::EffectRow::EMPTY
            },
            ContentNode::Unresolved(Sort::ValueType),
        ],
        "the edge closing the cycle becomes an unresolved leaf of its sort"
    );
    assert_eq!(
        formers(TypeContent::tabulated(&nodes, index(2_usize)).nodes()),
        [ContentNode::Abstract(Reference::Unoccupied)],
        "only what the root reaches is listed"
    );
    let dangling = [ContentNode::Case {
        scrutinee: index(usize::MAX),
        branches: vec![index(0_usize), index(usize::MAX)],
    }];
    assert_eq!(
        formers(TypeContent::tabulated(&dangling, index(0_usize)).nodes()),
        [
            ContentNode::Case {
                scrutinee: index(1_usize),
                branches: vec![index(2_usize), index(1_usize)],
            },
            ContentNode::Unresolved(Sort::Value),
            ContentNode::Unresolved(Sort::Computation),
        ],
        "an out-of-range child and a self-loop each become one unresolved leaf"
    );
}

#[test]
fn malformed_type_tables_fail_by_structure()
{
    let index = NodeIndex::from;
    let cases = [
        (vec![], seating::Absent::IllSorted),
        (
            vec![
                ContentNode::Product(vec![index(1_usize), index(usize::MAX)]),
                ContentNode::Product(Vec::new()),
            ],
            seating::Absent::Unresolved,
        ),
        (
            vec![
                ContentNode::Product(vec![index(1_usize), index(2_usize)]),
                ContentNode::Returner {
                    result: index(2_usize),
                    effects: gandr_core_term::effect::EffectRow::EMPTY,
                },
                ContentNode::Product(Vec::new()),
            ],
            seating::Absent::IllSorted,
        ),
        (
            vec![
                ContentNode::Arrow {
                    domain: index(1_usize),
                    codomain: index(1_usize),
                },
                ContentNode::Product(Vec::new()),
            ],
            seating::Absent::IllSorted,
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
            crate::fixture::type_content(&nodes).mint(arena, layout),
            Maybe::Absent(expected)
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
    let content = crate::fixture::type_content(&[ContentNode::Abstract(named)]);
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
    let absent = crate::fixture::type_content(&[ContentNode::Abstract(Reference::Item {
        key: ItemKey::from("repeated"),
        occurrence: Occurrence::from(2_usize),
    })]);
    let (arena, layout) = program.parts_mut();
    assert_eq!(
        absent.mint(arena, layout),
        Maybe::Absent(seating::Absent::Unplaced)
    );
}

/// The variables a probe names under a former's binders: intuitionistic
/// indices, then linear ones.
type Selection = (&'static [u32], &'static [u32]);

/// The tree a de Bruijn table spells from its first entry, in pre-order,
/// each former with its child wiring erased: two tables spell one tree
/// exactly when they differ only in numbering and sharing. Children are
/// enumerated by `map_children`, not by `ContentNode::children`, so a child
/// the supports' walk omits still shows; a wiring that loops stops the walk
/// with an unresolved leaf rather than spelling forever.
///
/// # Specification
/// trivial.
fn unfolded(table: &[ContentNode]) -> Vec<ContentNode>
{
    /// The longest spelling a probe table can have.
    const BOUND: usize = 4096;
    let mut spelled = Vec::new();
    let mut pending = vec![NodeIndex::from(0_usize)];
    while let Some(index) = pending.pop() {
        let Some(node) = table
            .get(usize::from(index))
            .filter(|_| spelled.len() < BOUND)
        else {
            spelled.push(ContentNode::Unresolved(Sort::Value));
            continue;
        };
        let first = pending.len();
        spelled.push(super::map_children(node, &mut |child| {
            pending.push(child);
            NodeIndex::default()
        }));
        pending
            .get_mut(first ..)
            .into_iter()
            .for_each(<[NodeIndex]>::reverse);
    }
    spelled
}

/// The de Bruijn table rooted at `former` whose every child is a probe of
/// its slot's sort naming every variable the slot binds, the intuitionistic
/// variable one past them and the linear variable just past them: ambient
/// `v1` and `ℓ0` wherever the probe stands. The children are the ones
/// `map_children` names; each slot's sort and binders are read from the
/// former's crossed children, and a child those omit is probed with a closed
/// leaf no other probe spells, so the omission shows in the projection.
///
/// # Specification
/// - requires: `former`'s children are distinct placeholders.
/// - ensures: the root is `former` with each placeholder replaced by its probe;
///   probes follow the root.
///
/// # Adequacy
/// - hypothesis: L3 — a crossing one short or one long in either zone moves a
///   probe's variables out of or into the root's support; a child the crossed
///   walk omits keeps a wiring the projection cannot place.
/// - witness: `content::tests::covers_preserve_every_binding_former`
/// - witness: `content::tests::projection_keeps_every_variadic_child`
#[spec(ensures: |ret| ret.len() > 1 || former.children().iter().next().is_none())]
fn probed(former: &ContentNode) -> Vec<ContentNode>
{
    use gandr_core_term::Zone;
    use gandr_core_term::support::Crossing;
    use gandr_kernel_term::DeBruijnIndex;
    let mut table = vec![former.clone()];
    let mut images: Vec<(NodeIndex, NodeIndex)> = Vec::new();
    let push = |table: &mut Vec<ContentNode>, node: ContentNode| {
        table.push(node);
        NodeIndex::from(table.len().saturating_sub(1))
    };
    let mut crossed: alloc::collections::BTreeMap<NodeIndex, (Sort, Crossing)> =
        alloc::collections::BTreeMap::new();
    for (child, sort, crossing) in former.children().crossed() {
        let _first = crossed.entry(child).or_insert((sort, crossing));
    }
    let mut placeholders = Vec::new();
    let _named = super::map_children(former, &mut |child| {
        placeholders.push(child);
        child
    });
    for placeholder in placeholders {
        let Some(&(sort, crossing)) = crossed.get(&placeholder)
        else {
            // A child the crossed walk omits: a closed leaf no probe spells,
            // so wherever the projection wires it instead shows.
            images.push((
                placeholder,
                push(&mut table, ContentNode::Base(BaseType::String)),
            ));
            continue;
        };
        let depth =
            |zone| u32::try_from(usize::from(crossing.depth(zone))).expect("a small crossing");
        let bound = depth(Zone::Intuitionistic);
        let mut variables: Vec<NodeIndex> = (0 .. bound)
            .chain([bound.saturating_add(1)])
            .map(|index| {
                push(&mut table, ContentNode::Variable {
                    zone: Zone::Intuitionistic,
                    index: DeBruijnIndex::from(index),
                })
            })
            .collect();
        variables.extend((0 ..= depth(Zone::Linear)).map(|index| {
            push(&mut table, ContentNode::Variable {
                zone: Zone::Linear,
                index: DeBruijnIndex::from(index),
            })
        }));
        let tuple = push(&mut table, ContentNode::Tuple(variables));
        let probe = match sort {
            Sort::Value => tuple,
            Sort::Computation => push(&mut table, ContentNode::Return(tuple)),
            Sort::ValueType => push(&mut table, ContentNode::Element {
                code: tuple,
                target: Level::zero(),
            }),
            Sort::CompType => push(&mut table, ContentNode::ComputationElement {
                code: tuple,
                target: Level::zero(),
            }),
        };
        images.push((placeholder, probe));
    }
    let root = super::map_children(former, &mut |placeholder| {
        images
            .iter()
            .find(|&&(seen, _)| seen == placeholder)
            .map_or(placeholder, |&(_, probe)| probe)
    });
    if let Some(slot) = table.first_mut() {
        *slot = root;
    }
    table
}

#[test]
fn covers_preserve_every_binding_former()
{
    use alloc::collections::BTreeMap;
    use alloc::sync::Arc;

    use gandr_core_term::ComponentCount;
    use gandr_core_term::FieldLabel;
    use gandr_core_term::Zone;
    use gandr_core_term::control::EffectClause;
    use gandr_core_term::effect::OperationName;
    use gandr_core_term::memory::AccessMode;
    use gandr_core_term::memory::MemoryForm;
    use gandr_core_term::session::SessionAction;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::FixpointEvidence;

    let index = NodeIndex::from;
    let at = DeBruijnIndex::from;
    let signature = probe_signature;
    let clauses = || {
        Arc::from([EffectClause {
            operation: OperationName::from("ask"),
            body: index(3_usize),
        }])
    };
    let label = |text: &str| FieldLabel::from(alloc::string::String::from(text));
    let both: Selection = (&[1], &[0]);
    let linear: Selection = (&[], &[0]);
    let cases: Vec<(&str, ContentNode, Selection)> = vec![
        (
            "static lambda",
            ContentNode::StaticLambda(index(1_usize)),
            both,
        ),
        ("lambda", ContentNode::Lambda(index(1_usize)), both),
        (
            "fixpoint",
            ContentNode::Fixpoint {
                body: index(1_usize),
                evidence: FixpointEvidence::Partial,
            },
            both,
        ),
        (
            "bind",
            ContentNode::Bind(index(1_usize), index(2_usize)),
            both,
        ),
        (
            "case",
            ContentNode::Case {
                scrutinee: index(1_usize),
                branches: vec![index(2_usize), index(3_usize)],
            },
            both,
        ),
        (
            "data case",
            ContentNode::DataCase {
                scrutinee: index(1_usize),
                motive: index(2_usize),
                branches: vec![index(3_usize)],
            },
            both,
        ),
        (
            "split",
            ContentNode::Split(
                index(1_usize),
                ComponentCount::from(3_usize),
                index(2_usize),
            ),
            both,
        ),
        (
            "dependent split",
            ContentNode::DependentSplit {
                scrutinee: index(1_usize),
                arity: ComponentCount::from(2_usize),
                motive: index(2_usize),
                body: index(3_usize),
            },
            both,
        ),
        ("shift", ContentNode::Shift(index(1_usize)), both),
        (
            "handle",
            ContentNode::Handle {
                signature: signature(),
                subject: index(1_usize),
                on_return: index(2_usize),
                clauses: clauses(),
            },
            both,
        ),
        (
            "scope",
            ContentNode::Scope {
                signature: signature(),
                subject: index(1_usize),
                on_return: index(2_usize),
                clauses: clauses(),
            },
            both,
        ),
        (
            "list fold",
            ContentNode::ListFold {
                element: index(1_usize),
                result: index(2_usize),
                list: index(3_usize),
                on_nil: index(4_usize),
                on_cons: index(5_usize),
            },
            both,
        ),
        (
            "list case",
            ContentNode::ListCase {
                list: index(1_usize),
                on_nil: index(2_usize),
                on_cons: index(3_usize),
            },
            both,
        ),
        (
            "element transport",
            ContentNode::ElementTransport {
                motive: index(1_usize),
                path: index(2_usize),
                value: index(3_usize),
            },
            both,
        ),
        (
            "ride",
            ContentNode::Ride {
                motive: index(1_usize),
                flow: index(2_usize),
                value: index(3_usize),
            },
            both,
        ),
        (
            "sigma",
            ContentNode::Sigma {
                first: index(1_usize),
                second: index(2_usize),
            },
            both,
        ),
        (
            "pi",
            ContentNode::Pi {
                domain: index(1_usize),
                codomain: index(2_usize),
            },
            both,
        ),
        (
            "fork",
            ContentNode::Session(SessionAction::Fork {
                protocol: index(1_usize),
                child: index(2_usize),
                parent: index(3_usize),
            }),
            both,
        ),
        (
            "hold",
            ContentNode::Memory(MemoryForm::Hold {
                value: index(1_usize),
                body: index(2_usize),
                grade: gandr_core_term::memory::HoldGrade::Many,
            }),
            both,
        ),
        (
            "access",
            ContentNode::Memory(MemoryForm::Access {
                mode: AccessMode::Exclusive {
                    unwind: index(2_usize),
                },
                held: at(0_u32),
                place: gandr_core_term::memory::Place::Whole,
                body: index(1_usize),
            }),
            both,
        ),
        (
            "shared access",
            ContentNode::Memory(MemoryForm::Access {
                mode: AccessMode::Shared,
                held: at(0_u32),
                place: gandr_core_term::memory::Place::Whole,
                body: index(1_usize),
            }),
            both,
        ),
        (
            "access at a place",
            ContentNode::Memory(MemoryForm::Access {
                mode: AccessMode::Exclusive {
                    unwind: index(2_usize),
                },
                held: at(0_u32),
                place: gandr_core_term::memory::Place::At {
                    index: index(2_usize),
                },
                body: index(1_usize),
            }),
            both,
        ),
        (
            "intuitionistic variable",
            ContentNode::Variable {
                zone: Zone::Intuitionistic,
                index: at(1_u32),
            },
            (&[1], &[]),
        ),
        (
            "linear variable",
            ContentNode::Variable {
                zone: Zone::Linear,
                index: at(0_u32),
            },
            linear,
        ),
        (
            "send",
            ContentNode::Session(SessionAction::Send {
                endpoint: at(0_u32),
                payload: index(1_usize),
            }),
            both,
        ),
        (
            "receive",
            ContentNode::Session(SessionAction::Receive {
                endpoint: at(0_u32),
            }),
            linear,
        ),
        (
            "select",
            ContentNode::Session(SessionAction::Select {
                endpoint: at(0_u32),
                label: label("a"),
            }),
            linear,
        ),
        (
            "offer",
            ContentNode::Session(SessionAction::Offer {
                endpoint: at(0_u32),
                arms: BTreeMap::from([(label("a"), index(1_usize)), (label("b"), index(2_usize))]),
            }),
            both,
        ),
        (
            "close",
            ContentNode::Session(SessionAction::Close {
                endpoint: at(0_u32),
            }),
            linear,
        ),
        (
            "resume",
            ContentNode::Memory(MemoryForm::Resume {
                view: at(0_u32),
                value: index(1_usize),
            }),
            both,
        ),
        (
            "abort",
            ContentNode::Memory(MemoryForm::Abort { view: at(0_u32) }),
            linear,
        ),
    ];
    assert_projects_back(
        cases
            .into_iter()
            .map(|(name, former, selection)| ProjectionCase(name, former, selection)),
    );
}

/// The interface the effect formers' probes carry: one operation whose
/// payload and reply types are the placeholders `4` and `5`.
///
/// # Specification
/// trivial.
fn probe_signature() -> gandr_core_term::effect::EffectSig<NodeIndex>
{
    use gandr_core_term::effect::EffectName;
    use gandr_core_term::effect::EffectOp;
    use gandr_core_term::effect::EffectSig;
    use gandr_core_term::effect::OperationName;
    EffectSig::new(EffectName::from("Probe"), [EffectOp {
        name: OperationName::from("ask"),
        payload: NodeIndex::from(4_usize),
        reply: NodeIndex::from(5_usize),
    }])
    .expect("one operation")
}

/// One projection case: its name in a failure message, the former probed and
/// the ambient variables its root selects.
struct ProjectionCase(&'static str, ContentNode, Selection);

/// Probe each former, tabulate it and project it back: the projection spells
/// the probe table's tree, and the root selects exactly the case's ambient
/// variables.
///
/// # Specification
/// trivial.
fn assert_projects_back(cases: impl IntoIterator<Item = ProjectionCase>)
{
    use gandr_core_term::Zone;
    use gandr_kernel_term::DeBruijnIndex;
    let at = DeBruijnIndex::from;
    for ProjectionCase(name, former, (intuitionistic, linear)) in cases {
        let table = probed(&former);
        let content = TypeContent::tabulated(&table, NodeIndex::from(0_usize));
        let projected = content.debruijn().expect("every index is in range");
        assert_eq!(
            unfolded(&projected),
            unfolded(&table),
            "{name}: every index projects back to itself"
        );
        assert!(
            content
                .root()
                .indices(Zone::Intuitionistic)
                .eq(intuitionistic.iter().copied().map(at)),
            "{name}: only the ambient intuitionistic variable is free"
        );
        assert!(
            content
                .root()
                .indices(Zone::Linear)
                .eq(linear.iter().copied().map(at)),
            "{name}: only the ambient linear variable is free"
        );
    }
}

#[test]
fn projection_keeps_every_variadic_child()
{
    use alloc::sync::Arc;

    use gandr_core_term::effect::OperationName;
    use gandr_core_term::session::RecordedMove;

    let index = NodeIndex::from;
    let both: Selection = (&[1], &[0]);
    // Interface types, a handler with no clause and recorded payloads sit
    // in variadic slots, walked only when the former carries them.
    let cases: Vec<(&str, ContentNode, Selection)> = vec![
        (
            "perform",
            ContentNode::Perform {
                signature: probe_signature(),
                operation: OperationName::from("ask"),
                payload: index(1_usize),
            },
            both,
        ),
        (
            "exercise",
            ContentNode::Exercise {
                capability: index(1_usize),
                signature: probe_signature(),
                operation: OperationName::from("ask"),
                payload: index(2_usize),
            },
            both,
        ),
        (
            "handle without clauses",
            ContentNode::Handle {
                signature: probe_signature(),
                subject: index(1_usize),
                on_return: index(2_usize),
                clauses: Arc::from([]),
            },
            both,
        ),
        (
            "recorded",
            ContentNode::Recorded(Arc::from([
                RecordedMove::Sent(index(1_usize)),
                RecordedMove::Closed,
                RecordedMove::Received(index(2_usize)),
            ])),
            both,
        ),
    ];
    assert_projects_back(
        cases
            .into_iter()
            .map(|(name, former, selection)| ProjectionCase(name, former, selection)),
    );
}

#[test]
fn unused_binder_interleavings_share_one_node()
{
    use gandr_core_term::Zone;
    use gandr_kernel_term::DeBruijnIndex;
    let mut arena = CoreArena::new();
    let variable = |arena: &mut CoreArena, index: u32| {
        arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index))
    };
    // (v0, v2) under three binders and (v1, v3) under four name the same
    // two ambient variables, interleaved with different unused binders.
    let a0 = variable(&mut arena, 0);
    let a2 = variable(&mut arena, 2);
    let first = arena.value_tuple(&[a0, a2]);
    let b1 = variable(&mut arena, 1);
    let b3 = variable(&mut arena, 3);
    let second = arena.value_tuple(&[b1, b3]);
    let reversed = arena.value_tuple(&[a2, a0]);
    let repeated = arena.value_tuple(&[a0, a0]);
    let mut left = first;
    for _ in 0_usize .. 3_usize {
        left = arena.value_static_lambda(left);
    }
    let mut right = second;
    for _ in 0_usize .. 4_usize {
        right = arena.value_static_lambda(right);
    }
    let alternatives = arena.value_tuple(&[reversed, repeated]);
    let placed = arena.value_tuple(&[left, right]);
    let root = arena.value_tuple(&[placed, alternatives]);
    let program = single(
        arena,
        Maybe::Absent(signature::Absent::Unsigned),
        Maybe::Present(root),
    );
    let encoded = encode_item(
        program.arena(),
        program.layout(),
        ItemOrdinal::from(0_usize),
    );
    let site = |node| encoded.sites.of(super::ArenaNode::Value(node));
    assert_eq!(
        site(first),
        site(second),
        "the two interleavings are one compact pair"
    );
    assert_ne!(site(first), site(reversed), "the cover keeps the wiring");
    assert_ne!(
        site(first),
        site(repeated),
        "one variable twice is not two variables"
    );
    let Maybe::Present(shared) = site(first)
    else {
        panic!("the pair is reached");
    };
    let node = encoded
        .content
        .nodes()
        .get(usize::from(shared))
        .expect("the compact pair");
    assert_eq!(
        (
            usize::from(node.scope().width(Zone::Intuitionistic)),
            usize::from(node.scope().width(Zone::Linear))
        ),
        (2, 0),
        "the pair is scoped by its two variables alone"
    );
    assert_eq!(
        node.cover()
            .iter()
            .map(|edge| edge.indices(Zone::Intuitionistic).collect::<Vec<_>>())
            .collect::<Vec<_>>(),
        [vec![DeBruijnIndex::from(0_u32)], vec![DeBruijnIndex::from(
            1_u32
        )]]
    );
    for subterm in [left, right, reversed, repeated] {
        let mut encoder = super::Encoder::new(program.arena(), program.layout());
        let _root = encoder.discover(super::ArenaNode::Value(subterm));
        encoder.drain();
        let content = TypeContent::of(
            program.arena(),
            program.layout(),
            super::ArenaNode::Value(subterm),
        );
        assert_eq!(
            content.debruijn().map(|table| unfolded(&table)),
            Ok(unfolded(&encoder.nodes)),
            "every ambient index is recovered"
        );
    }
    // The same two interleavings behind twenty distinct literals: the table
    // has outgrown the interner's linear search when the pairs arrive, so
    // they meet through its hashed index.
    let mut arena = CoreArena::new();
    let literals: Vec<ValueId> = (1_usize ..= 20_usize)
        .map(|n| {
            arena.value_literal(Literal::Integer(IntegerLiteral::new(
                Sign::NonNegative,
                Magnitude::from_decimal_text(alloc::format!("{n}")).expect("decimal digits"),
            )))
        })
        .collect();
    let padding = arena.value_tuple(&literals);
    let a0 = variable(&mut arena, 0);
    let a2 = variable(&mut arena, 2);
    let first = arena.value_tuple(&[a0, a2]);
    let b1 = variable(&mut arena, 1);
    let b3 = variable(&mut arena, 3);
    let second = arena.value_tuple(&[b1, b3]);
    let left = arena.value_static_lambda(first);
    let right = arena.value_static_lambda(second);
    let right = arena.value_static_lambda(right);
    let root = arena.value_tuple(&[padding, left, right]);
    let program = single(
        arena,
        Maybe::Absent(signature::Absent::Unsigned),
        Maybe::Present(root),
    );
    let encoded = encode_item(
        program.arena(),
        program.layout(),
        ItemOrdinal::from(0_usize),
    );
    assert!(
        encoded.content.nodes().len() > 20,
        "the padding fills the table first"
    );
    assert_eq!(
        encoded.sites.of(super::ArenaNode::Value(first)),
        encoded.sites.of(super::ArenaNode::Value(second)),
        "past the linear search, the two interleavings are still one pair"
    );
}

#[test]
fn open_roots_project_under_their_own_supports()
{
    use gandr_core_term::Zone;
    use gandr_kernel_term::DeBruijnIndex;

    use super::AbstractRoots;
    use super::DataContent;
    use super::DataRoots;
    use super::DeclarationRoots;

    let index = NodeIndex::from;
    let variable = |at: u32| ContentNode::Variable {
        zone: Zone::Intuitionistic,
        index: DeBruijnIndex::from(at),
    };
    let element = |code: usize| ContentNode::Element {
        code: index(code),
        target: Level::zero(),
    };
    // `T (A : Integer) = c (x : El A) (y : El (x, A))`: the fields are scoped
    // under the parameter and the fields before them, so `x` selects `v0`
    // and `y` selects `v0` and `v1`. An unreached entry comes first, so no
    // root keeps its raw index.
    let raw = [
        ContentNode::Base(BaseType::String),
        element(5),
        element(6),
        ContentNode::Base(BaseType::Integer),
        ContentNode::Product(Vec::new()),
        variable(0),
        ContentNode::Tuple(vec![index(5_usize), index(7_usize)]),
        variable(1),
    ];
    let data = DataRoots {
        parameters: vec![index(3_usize)],
        indices: Vec::new(),
        results: Vec::new(),
        constructors: vec![vec![index(1_usize), index(2_usize)]],
        kind: index(4_usize),
        presentation: gandr_core_term::Presentation::new(Vec::new()),
    };
    let selected = |content: &[gandr_core_term::support::Thinning]| {
        content
            .iter()
            .map(|support| support.indices(Zone::Intuitionistic).collect::<Vec<_>>())
            .collect::<Vec<_>>()
    };
    let expected = vec![
        vec![],
        vec![DeBruijnIndex::from(0_u32)],
        vec![DeBruijnIndex::from(0_u32), DeBruijnIndex::from(1_u32)],
        vec![],
    ];
    assert_eq!(
        selected(DataContent::tabulated(&data, &raw).placements()),
        expected,
        "a signature keeps each root's support, parameter, fields, then kind"
    );
    let item =
        crate::fixture::item_content(Reference::Unoccupied, &DeclarationRoots::Data(data), &raw);
    assert_eq!(
        selected(item.placements()),
        expected,
        "and so does its item"
    );
    let spelled: Vec<_> = item
        .declaration()
        .iter()
        .map(|(root, _)| item.debruijn(root))
        .collect();
    assert_eq!(
        spelled,
        [
            Ok(vec![ContentNode::Base(BaseType::Integer)]),
            Ok(vec![element(1), variable(0)]),
            Ok(vec![
                element(1),
                ContentNode::Tuple(vec![index(2_usize), index(3_usize)]),
                variable(0),
                variable(1),
            ]),
            Ok(vec![ContentNode::Product(Vec::new())]),
        ],
        "each root projects under its own support"
    );
    let sealed = crate::fixture::item_content(
        Reference::Unoccupied,
        &DeclarationRoots::Abstract(AbstractRoots {
            kind: index(4_usize),
            representation: index(3_usize),
            extent: gandr_kernel_term::SealExtent::from(0_usize),
            site: gandr_core_checker::SealSite::new(
                gandr_core_checker::SealingSite::from(0_usize),
                gandr_core_checker::ComponentOrdinal::from(0_usize),
            ),
            mobility: gandr_core_checker::worlds::Mobility::Immobile,
        }),
        &raw,
    );
    let DeclarationRoots::Abstract(roots) = *sealed.declaration()
    else {
        panic!("an abstract declaration stays abstract");
    };
    assert_eq!(
        [
            sealed.debruijn(roots.kind),
            sealed.debruijn(roots.representation)
        ],
        [
            Ok(vec![ContentNode::Product(Vec::new())]),
            Ok(vec![ContentNode::Base(BaseType::Integer)]),
        ],
        "an abstract type's renumbered roots name its kind and representation"
    );
}

#[test]
fn debruijn_projection_reports_index_overflow()
{
    use gandr_core_term::Zone;
    use gandr_core_term::support::PlacementError;
    use gandr_core_term::support::Thinning;
    use gandr_kernel_term::DeBruijnIndex;
    let ceiling = ContentNode::Variable {
        zone: Zone::Intuitionistic,
        index: DeBruijnIndex::from(u32::MAX),
    };
    let raw = [ContentNode::StaticLambda(NodeIndex::from(1_usize)), ceiling];
    let mut content = TypeContent::tabulated(&raw, NodeIndex::from(0_usize));
    assert_eq!(
        content.debruijn(),
        Ok(raw.to_vec()),
        "the ceiling under a binder is representable"
    );
    content.root =
        Thinning::from_ascending(&[DeBruijnIndex::from(u32::MAX)], &[]).expect("one index");
    assert_eq!(
        content.debruijn(),
        Err(PlacementError::IndexOverflow),
        "a support at the ceiling under a binder overflows rather than saturating"
    );
}
