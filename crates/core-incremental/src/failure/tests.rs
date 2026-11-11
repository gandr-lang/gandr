use alloc::string::String;
use alloc::vec;

use gandr_core_checker::CheckBudget;
use gandr_core_checker::CheckRefusal;
use gandr_core_checker::Declaration;
use gandr_core_checker::Mismatch;
use gandr_core_checker::OriginToken;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::Literal;
use gandr_kernel_term::StringLiteral;
use quenchant_shape::shape::Maybe;

use crate::boundary::ChildPosition;
use crate::boundary::ItemOrdinal;
use crate::boundary::Occurrence;
use crate::content::ArenaNode;
use crate::content::TypeContent;
use crate::content::anchors;
use crate::content::encode_item;
use crate::failure::Rooted;
use crate::region::Item;
use crate::region::ItemKey;
use crate::region::Program;
use crate::region::Reference;
use crate::typing::Projection;
use crate::typing::Typing;

/// The program `it : (Integer, Integer) = ("a", "a")`, beside its two text
/// literals: two nodes of one content, so one site of the item's table.
///
/// # Specification
/// trivial.
fn twin_literals() -> (Program, [ValueId; 2])
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let pair = arena.value_type_product(&[integer, integer]);
    let text = || Literal::Text(StringLiteral::new(String::from("a")));
    let first = arena.value_literal(text());
    let second = arena.value_literal(text());
    let body = arena.value_tuple(&[first, second]);
    let program = Program::new(arena, vec![Item::new(
        ItemKey::from("it"),
        Declaration::new(
            ConstantIndex::from(0_usize),
            Maybe::Present(pair),
            Maybe::Present(body),
            OriginToken::from(0_usize),
        ),
    )])
    .expect("one item ascends");
    (program, [first, second])
}

/// A refusal at one of two literals that share a site seats at that literal,
/// and the seated refusal and failure project back to the content the
/// checkpoint keeps.
#[test]
fn a_failure_seats_at_the_nodes_it_names()
{
    let (mut judged, _) = twin_literals();
    let resume =
        crate::check_program(&mut judged, CheckBudget::DEFAULT).expect("a one-item program checks");
    let Some(checkpoint) = resume.checkpoints().items().first()
    else {
        panic!("one item, one checkpoint");
    };
    let Maybe::Present(kept) = checkpoint.failure()
    else {
        panic!(
            "a refused item keeps its failure: {:?}",
            checkpoint.typing()
        );
    };
    let (fresh, [first, second]) = twin_literals();
    let mut arena = fresh.arena().clone();
    let Maybe::Present((refusal, failure)) =
        checkpoint.refused(&mut arena, (&fresh, ItemOrdinal::from(0_usize)))
    else {
        panic!("the failure seats in a fresh lowering");
    };
    let encoded = encode_item(&arena, fresh.layout(), ItemOrdinal::from(0_usize));
    let CheckRefusal::TypeMismatch(Mismatch::Value { at, .. }) = refusal
    else {
        panic!("the first literal mismatches its component: {refusal:?}");
    };
    assert!(
        at == first && at != second,
        "the refusal seats at the first literal, not at the second that shares its site"
    );
    let Maybe::Present(ref failure) = failure
    else {
        panic!("the failure seats beside the refusal");
    };
    let projection = Projection {
        arena: &arena,
        layout: fresh.layout(),
        sites: &encoded.sites,
        types: &crate::content::TypeMemo::default(),
        read: core::cell::RefCell::new(None),
    };
    assert_eq!(
        projection.typing(&gandr_core_checker::Verdict::Refused(refusal)),
        *checkpoint.typing(),
        "the seated refusal projects to the refusal the checkpoint keeps"
    );
    assert_eq!(
        projection.failed(refusal, Maybe::Present(failure), &[encoded
            .content
            .reference()]),
        *kept,
        "the seated failure projects to the content the checkpoint keeps"
    );
    assert!(
        matches!(checkpoint.typing(), &Typing::Refused(_)),
        "the item is refused"
    );
}

/// The program `a : (String, String) = ("a", "a")`, then `b : Integer = a`,
/// beside `a`'s signature: the type `b`'s refusal finds is a node of `a`.
///
/// # Specification
/// trivial.
fn mismatched_reference() -> (Program, ValueTypeId)
{
    let mut arena = CoreArena::new();
    let text = arena.value_type_base(BaseType::String);
    let texts = arena.value_type_product(&[text, text]);
    let literal = || Literal::Text(StringLiteral::new(String::from("a")));
    let first = arena.value_literal(literal());
    let second = arena.value_literal(literal());
    let tuple = arena.value_tuple(&[first, second]);
    let integer = arena.value_type_base(BaseType::Integer);
    let named = arena.value_constant(ConstantIndex::from(0_usize));
    let program = Program::new(arena, vec![
        Item::new(
            ItemKey::from("a"),
            Declaration::new(
                ConstantIndex::from(0_usize),
                Maybe::Present(texts),
                Maybe::Present(tuple),
                OriginToken::from(0_usize),
            ),
        ),
        Item::new(
            ItemKey::from("b"),
            Declaration::new(
                ConstantIndex::from(1_usize),
                Maybe::Present(integer),
                Maybe::Present(named),
                OriginToken::from(1_usize),
            ),
        ),
    ])
    .expect("two items ascend");
    (program, texts)
}

/// A refusal that finds the type of another item keeps that node at its
/// place under the other item's signature, and seats at that signature in a
/// fresh lowering rather than at a minted copy.
#[test]
fn a_node_of_another_item_seats_at_its_root()
{
    let (mut judged, _) = mismatched_reference();
    let resume =
        crate::check_program(&mut judged, CheckBudget::DEFAULT).expect("a two-item program checks");
    let Some(checkpoint) = resume.checkpoints().items().get(1)
    else {
        panic!("two items, two checkpoints");
    };
    let Maybe::Present(kept) = checkpoint.failure()
    else {
        panic!("the second item is refused: {:?}", checkpoint.typing());
    };
    assert!(
        kept.outside.iter().any(|outside| matches!(
            outside.rooted,
            Maybe::Present(Rooted { ref item, root, at })
                if *item == Reference::Item { key: ItemKey::from("a"), occurrence: Occurrence::from(0_usize) }
                    && usize::from(root) == 0_usize
                    && usize::from(at) == 0_usize
        )),
        "the found type is kept at the signature of `a`: {kept:?}"
    );
    let (fresh, signature) = mismatched_reference();
    let mut arena = fresh.arena().clone();
    let Maybe::Present((refusal, _)) =
        checkpoint.refused(&mut arena, (&fresh, ItemOrdinal::from(1_usize)))
    else {
        panic!("the failure seats in a fresh lowering");
    };
    let CheckRefusal::TypeMismatch(Mismatch::Value { synthesised, .. }) = refusal
    else {
        panic!("`a` mismatches the type `b` states: {refusal:?}");
    };
    assert_eq!(
        synthesised, signature,
        "the found type seats at the signature of `a`, not at a minted copy"
    );
}

/// A node outside an item that holds the item's body, whose two literals are
/// two nodes of one content, keeps the body as an anchor. Minted over the
/// anchor, it holds the body itself; minted alone, it holds a copy whose two
/// literals are one node, so no table that names the body names the copy.
#[test]
fn a_content_outside_the_item_mints_over_the_item_nodes_it_holds()
{
    let (mut program, [first, second]) = twin_literals();
    let encoded = encode_item(
        program.arena(),
        program.layout(),
        ItemOrdinal::from(0_usize),
    );
    let walk = encoded.sites.walk();
    let Some(body) = walk.iter().find_map(|&node| match node {
        ArenaNode::Value(id)
            if matches!(
                program.arena().value(id),
                Some(&Value::Tuple(ref held)) if **held == [first, second]
            ) =>
        {
            Some(id)
        },
        ArenaNode::Value(_)
        | ArenaNode::Computation(_)
        | ArenaNode::ValueType(_)
        | ArenaNode::CompType(_) => None,
    })
    else {
        panic!("the walk reaches the body: {walk:?}");
    };
    let (arena, layout) = program.parts_mut();
    let third = arena.value_literal(Literal::Text(StringLiteral::new(String::from("a"))));
    let outside = arena.value_tuple(&[body, third]);
    let kept = anchors(arena, layout, ArenaNode::Value(outside), &encoded.sites);
    let [ref anchor] = *kept
    else {
        panic!("the body alone is anchored: {kept:?}");
    };
    assert_eq!(
        anchor.path,
        vec![ChildPosition::from(0_usize)],
        "the body is the first child"
    );
    assert_eq!(
        walk.get(usize::from(anchor.at)),
        Some(&ArenaNode::Value(body)),
        "the anchor names the body's place in the walk"
    );
    let content = TypeContent::of(arena, layout, ArenaNode::Value(outside));
    let components = |arena: &CoreArena, minted| match minted {
        Maybe::Present(ArenaNode::Value(id)) => match arena.value(id) {
            Some(&Value::Tuple(ref held)) => held.to_vec(),
            other => panic!("the content mints a tuple: {other:?}"),
        },
        other @ (Maybe::Present(
            ArenaNode::Computation(_) | ArenaNode::ValueType(_) | ArenaNode::CompType(_),
        )
        | Maybe::Absent(_)) => panic!("the content mints a value: {other:?}"),
    };
    let held = [(anchor.path.as_slice(), ArenaNode::Value(body))];
    let over = content.mint_holding(arena, layout, &held);
    let over = components(arena, over);
    assert_eq!(
        over.first(),
        Some(&body),
        "minted over its anchor, it holds the body"
    );
    assert!(
        over.get(1).is_some_and(|&minted| minted != third),
        "a node the item does not hold is minted"
    );
    let alone = content.mint(arena, layout);
    let alone = components(arena, alone);
    let Some(&copy) = alone.first()
    else {
        panic!("the copy has a first component");
    };
    assert_ne!(copy, body, "minted alone, it holds a copy of the body");
    assert_ne!(
        components(arena, Maybe::Present(ArenaNode::Value(copy))),
        vec![first, second],
        "the copy's two literals are one node"
    );
}
