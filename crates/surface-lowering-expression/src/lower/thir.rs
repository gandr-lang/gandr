//! Signatures whose value is the staged THIR of a Rust function, as the
//! lowering reads them.
//!
//! A signature with no body owes its value. A `thir` mark names a Rust file
//! beside the source and a function of that file, and the function's body is
//! the value. The signature's type is `Expr` of `std.thir` at an item type.
//! Each constructor of the item type names the Rust function that a call of
//! it means, under an `item` mark:
//!
//! ```text
//! pub data Item : Type where
//!   @[item("identity")]
//!   | Identity : Item
//!   @[item("example")]
//!   | Example : Item
//!
//! @[thir(("example.rs", "example"))]
//! pub def exampleBody : Expr Item;
//! ```
//!
//! The dispatcher stages each mark before the lowering runs. The lowering
//! folds the staged nodes into constructors of `Expr`, each node after its
//! children. A mark that gives no body of the fragment is refused by name.
//!
//! - see: #8117

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Sign;
use gandr_runtime_rust_record::Body;
use gandr_runtime_rust_record::Node;
use gandr_runtime_rust_record::NodeIndex;
use gandr_runtime_rust_record::Staging;
use gandr_surface_lowering_base::lower::Context;
use quenchant_shape::shape::Maybe;

use super::Expressions;
use super::Families;
use super::Sink;
use crate::attribute::RegisteredAttribute;
use crate::attribute::texts;
use crate::error::LoweringRefusal;
use crate::error::StagedFault;
use crate::module::DeclarationSlot;
use crate::module::Half;
use crate::module::Operand;
use crate::module::Payload;
use crate::module::SlotIndex;
use crate::module::Standing;
use crate::origin::Origin;
use crate::resolve::SurfaceName;
use crate::unit::MarkIndex;
use crate::unit::Staged;
use crate::unit::UnitSource;
use crate::unit::Unstaged;

/// The module of the standard library that declares `Expr`.
const THIR_MODULE: &str = "std.thir";

/// The data type of THIR's expressions in [`THIR_MODULE`].
const EXPR: &str = "Expr";

/// The constructors of `Expr` that the fold mints, in the order of
/// [`Shape::tags`].
const NODES: [&str; 5] = ["Lit", "Param", "If", "Return", "Call"];

/// The type of a staged signature, `Expr` at an item type, and the tags that
/// the fold mints.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
struct Shape
{
    /// `Expr`'s declaration.
    expr: ConstantIndex,
    /// The declared type, `Expr` at the item type.
    declared: ValueTypeId,
    /// The tags of the constructors that [`NODES`] names, in its order.
    tags: [ConstructorTag; 5],
    /// The item type's declaration.
    item: ConstantIndex,
    /// The item type.
    item_type: ValueTypeId,
}

impl<'host, 'run: 'host, 'source: 'run, F: Families<'run, 'source>> Expressions<'host, F>
{
    /// Mint the value of each signature of the current source that a `thir`
    /// mark gives the staged body of a Rust function.
    ///
    /// # Specification
    /// - requires: the mint sweep has run, so each signature's type and each
    ///   mark's payload are minted.
    /// - ensures: each slot of the current source that holds no refusal and
    ///   carries a `thir` mark with a minted payload takes its declared type
    ///   and the staged body, as constructors of `Expr`, in the context's
    ///   natived. The slot takes the refusal of its mark instead, by the first
    ///   of these faults: the signature has a body; no staged answer matches
    ///   the mark's two texts; no reader is installed; the reader read no body;
    ///   the body is outside the fragment; the type is no `Expr` of `std.thir`
    ///   at a data type; a text of the item mark is no path and constructor of
    ///   the item type, or repeats one; a call names a path that the item mark
    ///   does not state.
    /// - panics: none.
    /// - executable: none — the minted values are the arena's, and a predicate
    ///   would fold each body again.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a staged body lowers to its constructors, and each
    ///   fault takes its own refusal.
    /// - witness: `gandr-surface-lowering::lower::thir::tests::a_staged_body_lowers_to_its_constructors_8117`
    /// - witness: `gandr-surface-lowering::lower::thir::tests::each_fault_of_a_thir_mark_is_refused_by_name_8117`
    ///
    /// # Cost
    /// - allocation: the texts of each mark's payload, setup
    /// - allocation: the minted declarations, growth within the source's slots
    /// - allocation: the item of each call, growth within the body's nodes
    /// - allocation: each node's constructor, its fields and its literal,
    ///   durable by the source
    /// - allocation: the refusal of a faulty mark, error path
    #[inline]
    pub fn mint_staged(
        &mut self,
        sink: &mut Sink<'_>,
    )
    {
        let cx = self.cx_mut();
        let mut minted = Vec::new();
        for (index, entry) in cx.collected.slots.iter().enumerate().skip(cx.current.slots) {
            if let Maybe::Present(_) = entry.refusal {
                continue;
            }
            let Some(mark) = entry
                .attributes
                .iter()
                .find(|written| written.name.as_ref() == RegisteredAttribute::THIR.as_ref())
            else {
                continue;
            };
            let Payload::Written(placed) = mark.payload
            else {
                continue;
            };
            let Maybe::Present(payload) = cx.value_at(placed.node)
            else {
                continue;
            };
            let staged = match entry.definition {
                Maybe::Present(_) => Err(StagedFault::Bodied),
                Maybe::Absent(_) => staged(cx, sink.arena, entry, payload),
            };
            let found = match staged {
                Ok((declared, root)) => {
                    let origin = Origin::new(entry.named.node, entry.named.span);
                    let _value = sink.value(root, origin);
                    Ok((declared, root))
                },
                Err(fault) => Err(LoweringRefusal::StagedBody {
                    span: mark.span,
                    fault,
                }),
            };
            minted.push((SlotIndex::from(index), found));
        }
        for (slot, found) in minted {
            match found {
                Ok(completed) => {
                    let _first = cx.natived.insert(slot, completed);
                },
                Err(refusal) => {
                    let _first = cx.faults.insert(slot, refusal);
                },
            }
        }
    }
}

/// The declared type of the staged signature `entry`, whose `thir` mark's
/// payload is `payload`, and its body as constructors of `Expr`.
///
/// # Specification
/// trivial.
///
/// # Errors
/// The fault of the mark, in the order that [`Expressions::mint_staged`]
/// states.
///
/// # Cost
/// - allocation: the texts of the payload, setup
/// - allocation: the item of each call, growth within the body's nodes
/// - allocation: each node's constructor, durable by the source
fn staged(
    cx: &Context<'_, '_>,
    arena: &mut CoreArena,
    entry: &DeclarationSlot<'_>,
    payload: ValueId,
) -> Result<(ValueTypeId, ValueId), StagedFault>
{
    let marks = cx
        .collected
        .unit
        .sources()
        .get(usize::from(cx.current.source))
        .map_or(&[][..], UnitSource::marks);
    let mark = answered(arena, payload, marks)?;
    let body = match marks.get(usize::from(mark)).map(|staged| &staged.staging) {
        Some(&Ok(Staging::Staged(ref body))) => body,
        Some(&Ok(Staging::Outside(_))) => return Err(StagedFault::Outside(mark)),
        Some(&Err(Unstaged::NoReader)) => return Err(StagedFault::NoReader),
        Some(&Err(Unstaged::Unread(_) | Unstaged::Refused(_))) | None => {
            return Err(StagedFault::Unread(mark));
        },
    };
    let Maybe::Present(Half {
        operand: Operand::Written(written),
        ..
    }) = entry.signature
    else {
        return Err(StagedFault::NotExpr);
    };
    let Maybe::Present(declared) = cx.value_type_at(written.node)
    else {
        return Err(StagedFault::NotExpr);
    };
    let shape = shape(cx, arena, declared)?;
    let calls = callees(cx, arena, &shape, body, mark)?;
    fold(arena, &shape, body, &calls, mark).map(|root| (declared, root))
}

/// The first of `marks` whose file and function are the two texts of
/// `payload`.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`StagedFault::Unanswered`] for a payload of no two texts, or for texts
/// that no mark holds.
///
/// # Cost
/// - allocation: the texts of the payload, setup
fn answered(
    arena: &CoreArena,
    payload: ValueId,
    marks: &[Staged],
) -> Result<MarkIndex, StagedFault>
{
    let Maybe::Present(written) = texts(arena, payload)
    else {
        return Err(StagedFault::Unanswered);
    };
    let [file, function] = *written.as_slice()
    else {
        return Err(StagedFault::Unanswered);
    };
    marks
        .iter()
        .position(|staged| {
            &*staged.file == file.as_ref() && staged.function.as_ref() == function.as_ref()
        })
        .map(MarkIndex::from)
        .ok_or(StagedFault::Unanswered)
}

/// The shape of `declared` when it is `Expr` of `std.thir` at a data type
/// with no parameter.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`StagedFault::NotExpr`] for any other type.
fn shape(
    cx: &Context<'_, '_>,
    arena: &CoreArena,
    declared: ValueTypeId,
) -> Result<Shape, StagedFault>
{
    let not = StagedFault::NotExpr;
    let Some(&ValueType::Data {
        declaration: expr,
        ref arguments,
        ..
    }) = arena.value_type(declared)
    else {
        return Err(not);
    };
    let [argument] = *arguments.as_slice()
    else {
        return Err(not);
    };
    let Some(&Value::Quote(item_type)) = arena.value(argument)
    else {
        return Err(not);
    };
    let Some(&ValueType::Data {
        declaration: item,
        arguments: ref parameters,
        ..
    }) = arena.value_type(item_type)
    else {
        return Err(not);
    };
    let family = SlotIndex::from(usize::from(expr));
    let Some(slot) = cx.collected.slots.get(usize::from(family))
    else {
        return Err(not);
    };
    let source = cx.collected.unit.source_at(slot.named.span.start());
    let homed = matches!(
        cx.collected.unit.home(source),
        Maybe::Present(home) if home.as_ref() == THIR_MODULE
    );
    if !homed || slot.name.as_ref() != EXPR || !parameters.is_empty() {
        return Err(not);
    }
    let mut tags = [ConstructorTag::from(0_usize); 5];
    for (tag, name) in tags.iter_mut().zip(NODES) {
        let Some(constructor) =
            cx.collected
                .constructors
                .get(&(source, SurfaceName::from(name), family))
        else {
            return Err(not);
        };
        *tag = ConstructorTag::from(constructor.tag);
    }
    Ok(Shape {
        expr,
        declared,
        tags,
        item,
        item_type,
    })
}

/// The tag of the item that each call of `body` names, in the order of the
/// calls, read from the `item` mark of each constructor of the shape's item
/// type.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`StagedFault::ItemMark`] for an item mark whose path is empty, that
/// stands on a constructor with fields, or whose path another constructor
/// states. [`StagedFault::Unmapped`] for the first call whose path no mark
/// states.
///
/// # Cost
/// - allocation: the map of the item marks, setup
/// - allocation: the item of each call, growth within the body's nodes
fn callees(
    cx: &Context<'_, '_>,
    arena: &CoreArena,
    shape: &Shape,
    body: &Body,
    mark: MarkIndex,
) -> Result<Vec<ConstructorTag>, StagedFault>
{
    let ill = StagedFault::ItemMark;
    let family = SlotIndex::from(usize::from(shape.item));
    let Some(slot) = cx.collected.slots.get(usize::from(family))
    else {
        return Err(ill);
    };
    let constructors: BTreeMap<_, _> = cx
        .collected
        .constructors
        .values()
        .filter(|constructor| constructor.family == family)
        .map(|constructor| (constructor.named, constructor))
        .collect();
    let mut items = BTreeMap::new();
    for written in slot
        .attributes
        .iter()
        .filter(|written| written.name.as_ref() == RegisteredAttribute::ITEM.as_ref())
    {
        let Standing::Constructor(named) = written.standing
        else {
            return Err(ill);
        };
        let Some(&constructor) = constructors.get(&named)
        else {
            return Err(ill);
        };
        let Payload::Written(placed) = written.payload
        else {
            return Err(ill);
        };
        let Maybe::Present(value) = cx.value_at(placed.node)
        else {
            return Err(ill);
        };
        let Maybe::Present(stated) = texts(arena, value)
        else {
            return Err(ill);
        };
        let [text] = stated[..]
        else {
            return Err(ill);
        };
        let path: &str = text.as_ref();
        if path.is_empty()
            || constructor.arity != 0
            || items
                .insert(path, ConstructorTag::from(constructor.tag))
                .is_some()
        {
            return Err(ill);
        }
    }
    body.nodes
        .iter()
        .zip(0_u32 ..)
        .filter_map(|(node, place)| match *node {
            Node::Call { ref callee, .. } => Some((callee, place)),
            Node::Literal(_) | Node::Parameter | Node::If { .. } | Node::Return(_) => None,
        })
        .map(|(callee, place)| {
            items
                .get(callee.as_ref())
                .copied()
                .ok_or_else(|| StagedFault::Unmapped {
                    mark,
                    node: NodeIndex::from(place),
                })
        })
        .collect()
}

/// `body` as constructors of `Expr`, each node after its children: the
/// root's value. The calls take the items of `calls` in order.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`StagedFault::Outside`] for an empty body, a child at or past its parent,
/// or a literal past the kernel's magnitudes.
///
/// # Cost
/// - allocation: the value of each node, growth within the body's nodes
/// - allocation: each node's constructor, its fields and its literal, durable
///   by the source
fn fold(
    arena: &mut CoreArena,
    shape: &Shape,
    body: &Body,
    calls: &[ConstructorTag],
    mark: MarkIndex,
) -> Result<ValueId, StagedFault>
{
    let outside = StagedFault::Outside(mark);
    let [literal, parameter, branch, returned, call] = shape.tags;
    let mut values: Vec<ValueId> = Vec::with_capacity(body.nodes.len());
    let mut items = calls.iter().copied();
    for node in &body.nodes {
        let child = |index: NodeIndex| {
            usize::try_from(u32::from(index))
                .ok()
                .and_then(|place| values.get(place).copied())
                .ok_or(outside)
        };
        let (tag, fields) = match *node {
            Node::Literal(written) => {
                let magnitude = Magnitude::from_decimal_text(alloc::format!(
                    "{}",
                    u128::from(written.magnitude)
                ))
                .ok_or(outside)?;
                let sign = match written.sign {
                    gandr_runtime_rust_record::Sign::Plus => Sign::NonNegative,
                    gandr_runtime_rust_record::Sign::Minus => Sign::Negative,
                };
                let value =
                    arena.value_literal(Literal::Integer(IntegerLiteral::new(sign, magnitude)));
                (literal, Vec::from([value]))
            },
            Node::Parameter => (parameter, Vec::new()),
            Node::If {
                condition,
                then,
                otherwise,
            } => (
                branch,
                Vec::from([child(condition)?, child(then)?, child(otherwise)?]),
            ),
            Node::Return(value) => (returned, Vec::from([child(value)?])),
            Node::Call { argument, .. } => {
                let argument = child(argument)?;
                let tag = items.next().ok_or(outside)?;
                let item = arena.value_constructor(shape.item, shape.item_type, tag, Vec::new());
                (call, Vec::from([item, argument]))
            },
        };
        values.push(arena.value_constructor(shape.expr, shape.declared, tag, fields));
    }
    values.last().copied().ok_or(outside)
}
