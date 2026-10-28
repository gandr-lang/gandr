//! Bridge mode: the fibre an introduction checked at a bridge type reads.
//!
//! `Bridge(A, a, b)` relates `a` and `b` parametrically. It has no
//! reflexivity, transport or eliminator of its own: an introduction form
//! checked there checks at the bridge's fibre, which [`fibre`] reads from the
//! carrier and the endpoints as the kernel's bridge fold reads them, clause for
//! clause, so every introduction the core admits the kernel readmits at its
//! bridge node:
//!
//! - a value universe: the relation type `U(El a → El b → F U)` at the
//!   universe's level;
//! - the unit type: the unit type;
//! - a base type: the unit type between equal literals, the empty sum between
//!   distinct ones;
//! - a binary product: the product of its components' fibres;
//! - a binary sum: the payloads' fibre between injections at one summand, the
//!   empty sum between injections at two;
//! - a list: the unit type between two nils, the empty sum between a nil and a
//!   cons, and between two conses the heads' fibre beside the tails' bridge,
//!   delayed;
//! - a free, unindexed data type whose fields are closed and never reach it:
//!   between one constructor its fields' fibres, right-nested, the unit type
//!   when it has none, and the empty sum between two;
//! - a function code: the bridge itself, which only `funext` introduces;
//! - an atom stating an interface: its relation between the endpoints.
//!
//! An endpoint the fold cannot read — a variable, a declared constant, a
//! returned computation — leaves the fibre unread, so the introduction checks
//! against the bridge as written, as one checked at an identity of an open type
//! does. The kernel names that fibre neutral.
//!
//! # Refusals
//!
//! The kernel's names. [`CheckRefusal::BridgeAtSealedType`] where a bridge's
//! carrier reaches a sealed atom that states no interface: the relation there
//! is the abstraction's to choose, so the bridge does not form
//! ([`require_unsealed`]). [`CheckRefusal::OutsideFold`] where an introduction
//! reads a carrier holding a code the fold has no clause for: a dependent or
//! effectful arrow, the path universe, an identity, a flow or a bridge, a
//! record, a sum or a product of an arity other than two, or a data type the
//! fold cannot read, holding itself among them.
//!
//! **Choice.** A fold of its own, reading the carrier's clauses and then the
//! endpoints, as the kernel's `identity_recursion::interpret` and its
//! evaluation do in bridge mode. **Alternative.** One fold with the kernel's
//! mode as a parameter. The core has no identity fold to share: an identity's
//! fibre is read in place, at the unit type, at a product and at an atom
//! (`Machine::identity_fibre`). **Reversal.** An identity fold in the core,
//! which this fold then becomes the bridge mode of.
//!
//! **Choice.** The endpoints are read as written, a declared constant
//! unfolding to nothing, because the kernel's fold reads its endpoints so and
//! names the fibre at a constant neutral. **Alternative.** Unfolding a declared
//! constant to its body, as an identity's endpoint is read; the kernel would
//! then refuse what the core admitted. **Reversal.** A kernel bridge fold that
//! unfolds its endpoints.
//!
//! # References
//!
//! - `vault:01a12317-ea29-7621-9f3f-2a6774805ca1` (vault) — lineage: bridges
//!   are structural and interval-free, so the fold grants no reflexivity of its
//!   own, no transport and no J, and an atom stating no interface has no
//!   bridge.

use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::ConstructorTag;
use gandr_core_term::Summand;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::effect::Purity;
use gandr_kernel_strata::Level;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::FieldPosition;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::Literal;
use quenchant_shape::shape::Maybe;

use crate::CheckRefusal;
use crate::CheckingContext;
use crate::view::CompTypeView;
use crate::view::ValueTypeView;
use crate::view::comp_type_view;
use crate::view::value_type_view;

/// A type the guard walk visits: a value type, or a computation type a thunk
/// holds.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Reached
{
    /// A value type.
    Value(ValueTypeId),
    /// A computation type.
    Computation(gandr_core_term::CompTypeId),
}

/// Refuse a bridge whose carrier reaches a sealed atom stating no interface.
///
/// # Specification
/// - requires: `carrier` is the carrier of the bridge type `at`.
/// - ensures: success exactly when every atom the carrier's type structure
///   reaches — through products, sums, lists, records, the arrows and results
///   of a thunk, and the carriers of identities, flows and bridges, never into
///   a code — states an interface.
/// - provides: the bridge's formation guard, the kernel's at its bridge node,
///   and the first guard of [`fibre`].
/// - fails: [`CheckRefusal::BridgeAtSealedType`] naming the bridge and the
///   first such atom; the unfolding's refusal.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Termination
/// - reason: a worklist over the finite type graph, each node visited once.
/// - measure: the nodes not yet visited.
///
/// # Adequacy
/// - hypothesis: L3 — a bridge at a sealed atom, at a function into it and at a
///   list of it refuses at formation, and one at an atom stating an interface
///   forms, in both checkers.
/// - witness: `bridge::tests::bridges::a_bridge_at_a_sealed_type_is_refused_by_name`
/// - witness: `bridge::tests::bridges::an_interfaced_atom_bears_its_relation_as_its_bridge_in_both_checkers`
#[spec(ensures: |ret| !matches!(ret, Err(CheckRefusal::BridgeAtSealedType { at: named, .. }) if named != at))]
pub fn require_unsealed(
    context: &mut CheckingContext<'_>,
    at: ValueTypeId,
    carrier: ValueTypeId,
) -> Result<(), CheckRefusal>
{
    let mut pending = Vec::from([Reached::Value(carrier)]);
    let mut seen = BTreeSet::new();
    while let Some(node) = pending.pop() {
        if !seen.insert(node) {
            continue;
        }
        match node {
            Reached::Value(ty) => {
                let ty = context.whnf_value_type(ty)?;
                match value_type_view(context.arena(), ty)? {
                    ValueTypeView::Abstract(atom) => {
                        if context.interface_of(atom).is_none() {
                            return Err(CheckRefusal::BridgeAtSealedType { at, atom });
                        }
                    },
                    ValueTypeView::Record(fields) => {
                        pending.extend(fields.values().map(|&field| Reached::Value(field)));
                    },
                    ValueTypeView::Product(parts) | ValueTypeView::Sum(parts) => {
                        pending.extend(parts.iter().map(|&part| Reached::Value(part)));
                    },
                    ValueTypeView::List(element)
                    | ValueTypeView::Path {
                        carrier: element, ..
                    }
                    | ValueTypeView::Flow {
                        carrier: element, ..
                    }
                    | ValueTypeView::Bridge {
                        carrier: element, ..
                    }
                    | ValueTypeView::Staged { base: element, .. }
                    | ValueTypeView::Kept { value: element, .. } => {
                        pending.push(Reached::Value(element));
                    },
                    ValueTypeView::Sigma { first, second }
                    | ValueTypeView::StaticPi {
                        domain: first,
                        codomain: second,
                    } => {
                        pending.extend([Reached::Value(first), Reached::Value(second)]);
                    },
                    ValueTypeView::Thunk(body) => pending.push(Reached::Computation(body)),
                    ValueTypeView::Data { .. }
                    | ValueTypeView::Stack { .. }
                    | ValueTypeView::PathUniverse(..)
                    | ValueTypeView::Run(_)
                    | ValueTypeView::Prefix(_)
                    | ValueTypeView::Dialogue(_)
                    | ValueTypeView::Web
                    | ValueTypeView::Integer
                    | ValueTypeView::String
                    | ValueTypeView::Character
                    | ValueTypeView::Float64
                    | ValueTypeView::Fixed(_)
                    | ValueTypeView::Unit
                    | ValueTypeView::Universe { .. }
                    | ValueTypeView::Lift { .. }
                    | ValueTypeView::Element { .. }
                    | ValueTypeView::Capability { .. }
                    | ValueTypeView::Buffer
                    | ValueTypeView::Session(_)
                    | ValueTypeView::World(_)
                    | ValueTypeView::Row
                    | ValueTypeView::RowTail(_)
                    | ValueTypeView::Unknown => {},
                }
            },
            Reached::Computation(ty) => match comp_type_view(context.arena(), ty)? {
                CompTypeView::Returner { result, .. } => pending.push(Reached::Value(result)),
                CompTypeView::Arrow { domain, codomain }
                | CompTypeView::Pi { domain, codomain } => {
                    pending.extend([Reached::Value(domain), Reached::Computation(codomain)]);
                },
                CompTypeView::With(parts) => {
                    pending.extend(parts.iter().map(|&part| Reached::Computation(part)));
                },
                CompTypeView::Element { .. }
                | CompTypeView::Unknown
                | CompTypeView::Codata { .. } => {},
            },
        }
    }
    Ok(())
}

/// One step of the evaluation [`fibre`] runs over its carrier and endpoints.
#[derive(Clone, Copy, Debug)]
enum Task
{
    /// Read the fibre at a code between two endpoints.
    Visit(ValueTypeId, ValueId, ValueId),
    /// The bridge at a list between two tails: the lifting's delayed step.
    Delay(ValueTypeId, ValueId, ValueId),
    /// Pair the last two fibres read as a product, the earlier first.
    Pair,
}

/// What [`fibre`] reads an introduction checked at a bridge as.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Fibre
{
    /// The type the introduction checks at.
    Read(ValueTypeId),
    /// No fibre: an endpoint is no canonical form the fold reads, or the
    /// carrier is a function code. The introduction checks against the bridge
    /// as written.
    Written,
}

/// The fibre an introduction `at` checked at `Bridge(carrier, left, right)`
/// checks at.
///
/// # Specification
/// - requires: the bridge is formed.
/// - ensures: the fold's fibre, clause for clause as the module states it;
///   [`Fibre::Written`] where an endpoint is no canonical form of its code, or
///   at the root of a function code.
/// - provides: the checking machine's redirect of an introduction checked at a
///   bridge.
/// - fails: as [`require_unsealed`]; [`CheckRefusal::OutsideFold`] at `at`,
///   naming the code, where the carrier holds a code the fold has no clause
///   for; [`CheckRefusal::MachineInvariant`] where a field's type is not the
///   one the fold read; the unfolding's refusal.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Termination
/// - reason: a stack of tasks, each visit reading the endpoints' canonical
///   forms one constructor deeper; a list's tails are delayed, never visited.
/// - measure: the endpoints' syntax below the forms visited.
///
/// # Adequacy
/// - hypothesis: L3 — a relation inhabits a bridge at the universe, a tuple of
///   relations one at a product of universes, a list's lifting one at a list,
///   and the relation's evidence one at an interfaced atom; a code outside the
///   fold refuses by name; each crosses to the kernel and is readmitted.
/// - witness: `bridge::tests::bridges::a_bridge_at_the_universe_is_a_relation_in_both_checkers`
/// - witness: `bridge::tests::bridges::a_bridge_at_a_list_is_the_relation_lifting_in_both_checkers`
/// - witness: `bridge::tests::bridges::the_codes_outside_the_bridge_fold_are_refused_by_name`
#[spec(ensures: |ret| !matches!(ret, Err(CheckRefusal::OutsideFold { at: named, .. }) if named != at))]
pub fn fibre(
    context: &mut CheckingContext<'_>,
    at: ValueId,
    (bridge, carrier, left, right): (ValueTypeId, ValueTypeId, ValueId, ValueId),
) -> Result<Fibre, CheckRefusal>
{
    require_unsealed(context, bridge, carrier)?;
    interpret(context, at, bridge, carrier)?;
    let carrier = context.whnf_value_type(carrier)?;
    if let ValueTypeView::Thunk(_) = value_type_view(context.arena(), carrier)? {
        return Ok(Fibre::Written);
    }
    let mut tasks = Vec::from([Task::Visit(carrier, left, right)]);
    let mut read: Vec<ValueTypeId> = Vec::new();
    while let Some(task) = tasks.pop() {
        let fibre = match task {
            Task::Pair => {
                let (Some(second), Some(first)) = (read.pop(), read.pop())
                else {
                    return Err(CheckRefusal::MachineInvariant);
                };
                context.arena_mut().value_type_product(&[first, second])
            },
            Task::Delay(list, tail, rest) => {
                context.arena_mut().value_type_bridge(list, tail, rest)
            },
            Task::Visit(code, left, right) => {
                match visit(
                    context,
                    (code, written(context, left), written(context, right)),
                )? {
                    Visit::Fibre(fibre) => fibre,
                    Visit::Then(steps) => {
                        tasks.extend(steps);
                        continue;
                    },
                    Visit::Neutral => return Ok(Fibre::Written),
                }
            },
        };
        read.push(fibre);
    }
    match *read.as_slice() {
        [fibre] => Ok(Fibre::Read(fibre)),
        _ => Err(CheckRefusal::MachineInvariant),
    }
}

/// What one visit of the fold reads.
#[derive(Debug)]
enum Visit
{
    /// The fibre, read at once.
    Fibre(ValueTypeId),
    /// The tasks it is read by, pushed in this order.
    Then(Vec<Task>),
    /// An endpoint is no canonical form of the code.
    Neutral,
}

/// The value `value` is read as at a bridge's endpoint: itself, through its
/// ascriptions and marks.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the first value of the chain of ascriptions and marks from
///   `value` that is neither.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// - reason: one `loop` peeling one wrapper per turn.
/// - measure: the wrappers around the value, finite syntax.
///
/// # Adequacy
/// - hypothesis: L3 — as [`fibre`], whose endpoints it reads.
/// - witness: `bridge::tests::bridges::a_bridge_at_a_list_is_the_relation_lifting_in_both_checkers`
#[spec(ensures: |ret| !matches!(context.arena().value(ret), Some(Value::Ascribe { .. } | Value::Mark { .. })))]
fn written(
    context: &CheckingContext<'_>,
    mut value: ValueId,
) -> ValueId
{
    loop {
        match context.arena().value(value) {
            Some(&Value::Ascribe { value: inner, .. } | &Value::Mark { body: inner, .. }) => {
                value = inner;
            },
            _ => return value,
        }
    }
}

/// The clause the fold reads at one code, owned past the arena's borrow.
#[derive(Clone, Debug)]
enum Clause
{
    /// The unit type.
    Unit,
    /// A base type, related by its literals.
    Discrete,
    /// A value universe at its level: relations between codes.
    Relation(Level),
    /// A binary product.
    Product(ValueTypeId, ValueTypeId),
    /// A binary sum.
    Sum(ValueTypeId, ValueTypeId),
    /// A list of its elements.
    List(ValueTypeId),
    /// A function code.
    Function,
    /// An atom stating an interface.
    Atom(ConstantIndex),
    /// A data type the fold reads.
    Data,
}

/// An endpoint's canonical form, as the fold reads it.
#[derive(Clone, Debug)]
enum Form
{
    /// A literal.
    Literal(Literal),
    /// A tuple of two components.
    Pair(ValueId, ValueId),
    /// An injection at a summand.
    Injection(Summand, ValueId),
    /// The empty list.
    Nil,
    /// A cons of a head and a tail.
    Cons(ValueId, ValueId),
    /// A constructor at its tag, with its fields.
    Constructor(ConstructorTag, Vec<ValueId>),
    /// No canonical form the fold reads.
    Neutral,
}

/// The clause the fold reads at the code `code`.
///
/// # Specification
/// - requires: `code` passed [`interpret`] and is a weak head.
/// - ensures: the module's clause for the code's former.
/// - fails: [`CheckRefusal::MachineInvariant`] at a former [`interpret`]
///   refuses.
/// - panics: none.
/// - executable: none — the clause is the module's table read at the code's
///   former, so a predicate would restate the match.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — as [`fibre`].
/// - witness: `bridge::tests::bridges::a_bridge_at_the_universe_is_a_relation_in_both_checkers`
fn clause(
    context: &CheckingContext<'_>,
    code: ValueTypeId,
) -> Result<Clause, CheckRefusal>
{
    Ok(match value_type_view(context.arena(), code)? {
        ValueTypeView::Unit => Clause::Unit,
        ValueTypeView::Integer
        | ValueTypeView::String
        | ValueTypeView::Character
        | ValueTypeView::Float64
        | ValueTypeView::Fixed(_) => Clause::Discrete,
        ValueTypeView::Universe {
            sort: GroundSort::Value,
            level,
        } => Clause::Relation(level.clone()),
        ValueTypeView::Product(&[first, second]) => Clause::Product(first, second),
        ValueTypeView::Sum(&[first, second]) => Clause::Sum(first, second),
        ValueTypeView::List(element) => Clause::List(element),
        ValueTypeView::Thunk(_) => Clause::Function,
        ValueTypeView::Abstract(atom) => Clause::Atom(atom),
        ValueTypeView::Data { .. } => Clause::Data,
        ValueTypeView::Record(_)
        | ValueTypeView::Stack { .. }
        | ValueTypeView::PathUniverse(..)
        | ValueTypeView::Path { .. }
        | ValueTypeView::Flow { .. }
        | ValueTypeView::Bridge { .. }
        | ValueTypeView::Run(_)
        | ValueTypeView::Prefix(_)
        | ValueTypeView::Dialogue(_)
        | ValueTypeView::Web
        | ValueTypeView::Sum(_)
        | ValueTypeView::Product(_)
        | ValueTypeView::Universe { .. }
        | ValueTypeView::Lift { .. }
        | ValueTypeView::Element { .. }
        | ValueTypeView::StaticPi { .. }
        | ValueTypeView::Sigma { .. }
        | ValueTypeView::Capability { .. }
        | ValueTypeView::Buffer
        | ValueTypeView::Session(_)
        | ValueTypeView::Staged { .. }
        | ValueTypeView::Kept { .. }
        | ValueTypeView::World(_)
        | ValueTypeView::Row
        | ValueTypeView::RowTail(_)
        | ValueTypeView::Unknown => return Err(CheckRefusal::MachineInvariant),
    })
}

/// The canonical form of the endpoint `value`, read through [`written`].
///
/// # Specification
/// - requires: nothing.
/// - ensures: the form `value`'s written head is, a tuple only of two
///   components; [`Form::Neutral`] for any other head.
/// - fails: never.
/// - panics: none.
/// - executable: none — the form is the endpoint's head, so a predicate would
///   restate the match.
///
/// # Adequacy
/// - hypothesis: L3 — as [`fibre`].
/// - witness: `bridge::tests::bridges::a_bridge_at_a_list_is_the_relation_lifting_in_both_checkers`
fn form(
    context: &CheckingContext<'_>,
    value: ValueId,
) -> Form
{
    match context.arena().value(written(context, value)) {
        Some(&Value::Literal(ref literal)) => Form::Literal(literal.clone()),
        Some(&Value::Tuple(ref components)) => match **components {
            [first, second] => Form::Pair(first, second),
            _ => Form::Neutral,
        },
        Some(&Value::Injection(summand, payload)) => Form::Injection(summand, payload),
        Some(&Value::ListNil) => Form::Nil,
        Some(&Value::ListCons(head, tail)) => Form::Cons(head, tail),
        Some(&Value::Constructor {
            tag, ref fields, ..
        }) => Form::Constructor(tag, fields.clone()),
        _ => Form::Neutral,
    }
}

/// One clause of the fold, at `code` between the endpoints `left` and `right`.
///
/// # Specification
/// - requires: `code` passed [`interpret`].
/// - ensures: the clause's fibre or the visits it is read by, as the module
///   states them; [`Visit::Neutral`] where an endpoint is no canonical form of
///   `code`.
/// - fails: [`CheckRefusal::MachineInvariant`] at a code [`interpret`] refuses,
///   or at a data type's field the fold did not read; the unfolding's refusal.
/// - panics: none.
/// - executable: none — the fibres are the module's clauses over arena nodes
///   this call mints, which no predicate reads back without restating them.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — as [`fibre`].
/// - witness: `bridge::tests::bridges::a_bridge_at_the_universe_is_a_relation_in_both_checkers`
/// - witness: `bridge::tests::bridges::a_bridge_at_a_list_is_the_relation_lifting_in_both_checkers`
fn visit(
    context: &mut CheckingContext<'_>,
    (code, left, right): (ValueTypeId, ValueId, ValueId),
) -> Result<Visit, CheckRefusal>
{
    let code = context.whnf_value_type(code)?;
    let read = clause(context, code)?;
    let (first, second) = (form(context, left), form(context, right));
    if let Clause::Atom(atom) = read {
        let Some((interface, kind)) = context.interface_of(atom)
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        let Some(&gandr_core_term::ValueType::Universe { ref level, .. }) =
            context.arena().value_type(kind)
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        let level = level.clone();
        return Ok(Visit::Fibre(crate::former::related_by(
            context.arena_mut(),
            interface.relation(),
            (left, right),
            level,
        )));
    }
    if let (
        &Clause::Data,
        &Form::Constructor(tag, ref lefts),
        &Form::Constructor(other, ref rights),
    ) = (&read, &first, &second)
        && tag == other
    {
        return constructor_fields(context, code, tag, (lefts, rights));
    }
    let arena = context.arena_mut();
    Ok(match (read, first, second) {
        (Clause::Unit, ..) | (Clause::List(_), Form::Nil, Form::Nil) => {
            Visit::Fibre(arena.value_type_unit())
        },
        (Clause::Discrete, Form::Literal(first), Form::Literal(second)) => {
            if first == second {
                Visit::Fibre(arena.value_type_unit())
            }
            else {
                Visit::Fibre(arena.value_type_sum(&[]))
            }
        },
        (Clause::Relation(level), ..) => {
            let first = arena.value_type_element(left, level.clone());
            let second = arena.value_type_element(right, level);
            let valued = arena.comp_type_returner(code);
            let inner = arena.comp_type_arrow(second, valued);
            let relation = arena.comp_type_arrow(first, inner);
            Visit::Fibre(arena.value_type_thunk(relation))
        },
        (
            Clause::Product(first, second),
            Form::Pair(left_first, left_second),
            Form::Pair(right_first, right_second),
        ) => Visit::Then(Vec::from([
            Task::Pair,
            Task::Visit(second, left_second, right_second),
            Task::Visit(first, left_first, right_first),
        ])),
        (
            Clause::Sum(first, second),
            Form::Injection(at, payload),
            Form::Injection(other, rest),
        ) => {
            if at != other {
                Visit::Fibre(arena.value_type_sum(&[]))
            }
            else if usize::from(at) == 0_usize {
                Visit::Then(Vec::from([Task::Visit(first, payload, rest)]))
            }
            else {
                Visit::Then(Vec::from([Task::Visit(second, payload, rest)]))
            }
        },
        (Clause::List(_), Form::Nil, Form::Cons(..))
        | (Clause::List(_), Form::Cons(..), Form::Nil)
        | (Clause::Data, Form::Constructor(..), Form::Constructor(..)) => {
            Visit::Fibre(arena.value_type_sum(&[]))
        },
        (Clause::List(element), Form::Cons(head, tail), Form::Cons(other, rest)) => {
            Visit::Then(Vec::from([
                Task::Pair,
                Task::Delay(code, tail, rest),
                Task::Visit(element, head, other),
            ]))
        },
        (Clause::Function, ..) => Visit::Fibre(arena.value_type_bridge(code, left, right)),
        (
            Clause::Discrete
            | Clause::Product(..)
            | Clause::Sum(..)
            | Clause::List(_)
            | Clause::Data
            | Clause::Atom(_),
            ..,
        ) => Visit::Neutral,
    })
}

/// The visits relating two constructors at one tag of the data type `code`:
/// their fields' fibres, right-nested with the first field outermost, the unit
/// type when the constructor has none.
///
/// # Specification
/// - requires: `code` is a data type [`interpret`] read, and both field lists
///   are a constructor's at `tag`.
/// - ensures: the unit type when the constructor has no field; otherwise one
///   pair fewer than fields above the fields' visits, the first field's on top,
///   each at the field's type read outside its constructor.
/// - fails: [`CheckRefusal::MachineInvariant`] at a field the fold did not read
///   or a tag the signature lacks; the signature's refusal.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — a constructor of two fields relates as the product of
///   their fibres, and one of none by the unit type.
/// - witness: `bridge::tests::bridges::a_bridge_at_a_data_type_relates_constructor_by_constructor`
#[spec(ensures: |ret| match ret {
    Ok(Visit::Then(ref steps)) => steps.len() == lefts.len().saturating_mul(2).saturating_sub(1),
    Ok(Visit::Fibre(_)) => lefts.is_empty(),
    Ok(_) => false,
    Err(_) => true,
})]
fn constructor_fields(
    context: &mut CheckingContext<'_>,
    code: ValueTypeId,
    tag: ConstructorTag,
    (lefts, rights): (&[ValueId], &[ValueId]),
) -> Result<Visit, CheckRefusal>
{
    if lefts.is_empty() {
        return Ok(Visit::Fibre(context.arena_mut().value_type_unit()));
    }
    let signature = crate::former::signature(context, code)?;
    let declared = signature
        .constructors()
        .get(usize::from(tag))
        .ok_or(CheckRefusal::MachineInvariant)?;
    if declared.len() != lefts.len() || declared.len() != rights.len() {
        return Err(CheckRefusal::MachineInvariant);
    }
    let mut steps = Vec::new();
    steps.resize_with(declared.len().saturating_sub(1), || Task::Pair);
    for (position, (&field, (&first, &second))) in declared
        .iter()
        .zip(lefts.iter().zip(rights))
        .enumerate()
        .rev()
    {
        let Maybe::Present(field) =
            crate::former::field_outside(context, code, field, FieldPosition::from(position))?
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        steps.push(Task::Visit(field, first, second));
    }
    Ok(Visit::Then(steps))
}

/// Read the carrier's clauses, refusing a code the fold has none for.
///
/// # Specification
/// - requires: the bridge `bridge` over `carrier` is formed.
/// - ensures: success exactly when every code the carrier holds is one the
///   module's clauses read: a data type's fields read in turn, a data type
///   reached again inside its own fields refused.
/// - provides: the clause table [`visit`] reads, checked before any endpoint is
///   read, as the kernel interprets the carrier before evaluating it.
/// - fails: [`CheckRefusal::OutsideFold`] at `at`, naming the first code
///   outside the fold; [`CheckRefusal::BridgeAtSealedType`] at a data type's
///   field reaching an atom that states no interface; the unfolding's refusal.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Termination
/// - reason: a worklist over the finite type graph; a data type is held open
///   while its fields are read and refused when reached again.
/// - measure: the nodes not yet read.
///
/// # Adequacy
/// - hypothesis: L3 — a dependent arrow, the path universe, a bridge at a
///   bridge, a ternary product and a data type holding itself each refuse by
///   name, and the codes the clauses read pass.
/// - witness: `bridge::tests::bridges::the_codes_outside_the_bridge_fold_are_refused_by_name`
#[spec(ensures: |ret| !matches!(ret, Err(CheckRefusal::OutsideFold { at: named, .. }) if named != at))]
fn interpret(
    context: &mut CheckingContext<'_>,
    at: ValueId,
    bridge: ValueTypeId,
    carrier: ValueTypeId,
) -> Result<(), CheckRefusal>
{
    let outside = |code| CheckRefusal::OutsideFold { at, code };
    let mut pending = Vec::from([(carrier, false)]);
    let mut read = BTreeSet::new();
    let mut expanding = BTreeSet::new();
    while let Some((written, expanded)) = pending.pop() {
        let code = context.whnf_value_type(written)?;
        if read.contains(&code) {
            continue;
        }
        match value_type_view(context.arena(), code)? {
            ValueTypeView::Unit
            | ValueTypeView::Integer
            | ValueTypeView::String
            | ValueTypeView::Character
            | ValueTypeView::Float64
            | ValueTypeView::Fixed(_)
            | ValueTypeView::Universe {
                sort: GroundSort::Value,
                ..
            } => {},
            ValueTypeView::Abstract(atom) => {
                if context.interface_of(atom).is_none() {
                    return Err(CheckRefusal::BridgeAtSealedType { at: bridge, atom });
                }
            },
            ValueTypeView::Product(&[first, second]) | ValueTypeView::Sum(&[first, second]) => {
                pending.extend([(first, false), (second, false)]);
            },
            ValueTypeView::List(element) => pending.push((element, false)),
            ValueTypeView::Thunk(body) => {
                let CompTypeView::Arrow { domain, codomain } =
                    comp_type_view(context.arena(), body)?
                else {
                    return Err(outside(code));
                };
                let CompTypeView::Returner { result, effects } =
                    comp_type_view(context.arena(), codomain)?
                else {
                    return Err(outside(code));
                };
                if effects.purity() != Purity::Pure {
                    return Err(outside(code));
                }
                pending.extend([(domain, false), (result, false)]);
            },
            ValueTypeView::Data { .. } => {
                if expanded {
                    expanding.remove(&code);
                }
                else {
                    if !expanding.insert(code) {
                        return Err(outside(code));
                    }
                    pending.push((code, true));
                    for field in data_fields(context, code)?.ok_or_else(|| outside(code))? {
                        pending.push((field, false));
                    }
                    continue;
                }
            },
            ValueTypeView::Record(_)
            | ValueTypeView::Stack { .. }
            | ValueTypeView::PathUniverse(..)
            | ValueTypeView::Path { .. }
            | ValueTypeView::Flow { .. }
            | ValueTypeView::Bridge { .. }
            | ValueTypeView::Run(_)
            | ValueTypeView::Prefix(_)
            | ValueTypeView::Dialogue(_)
            | ValueTypeView::Web
            | ValueTypeView::Sum(_)
            | ValueTypeView::Product(_)
            | ValueTypeView::Universe { .. }
            | ValueTypeView::Lift { .. }
            | ValueTypeView::Element { .. }
            | ValueTypeView::StaticPi { .. }
            | ValueTypeView::Sigma { .. }
            | ValueTypeView::Capability { .. }
            | ValueTypeView::Buffer
            | ValueTypeView::Session(_)
            | ValueTypeView::Staged { .. }
            | ValueTypeView::Kept { .. }
            | ValueTypeView::World(_)
            | ValueTypeView::Row
            | ValueTypeView::RowTail(_)
            | ValueTypeView::Unknown => return Err(outside(code)),
        }
        read.insert(code);
    }
    Ok(())
}

/// The field types of the data type `datatype`, when the fold reads it.
///
/// # Specification
/// - requires: `datatype` is a formed data type.
/// - ensures: every constructor's field types in tag and field order, each read
///   outside its constructor, when the declaration is unindexed, has a
///   constructor, presents no rule and no cell, and no field names a parameter
///   or a field before it; nothing otherwise, as the kernel's
///   `flow_universe::data_signature` reads it.
/// - fails: the signature's refusal.
/// - panics: none.
/// - executable: none — the conditions are the kernel's reading of a signature,
///   which a predicate would restate over the same signature.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — as [`interpret`], whose data clause it reads.
/// - witness: `bridge::tests::bridges::the_codes_outside_the_bridge_fold_are_refused_by_name`
fn data_fields(
    context: &mut CheckingContext<'_>,
    datatype: ValueTypeId,
) -> Result<Option<Vec<ValueTypeId>>, CheckRefusal>
{
    let signature = crate::former::signature(context, datatype)?;
    let presentation = signature.presentation();
    if signature.constructors().is_empty()
        || !signature.indices().is_empty()
        || !presentation.rules().is_empty()
        || presentation.cells().is_some()
    {
        return Ok(None);
    }
    let parameters = signature.parameters().len();
    let mut fields = Vec::new();
    for constructor in signature.constructors() {
        for (position, &field) in constructor.iter().enumerate() {
            let scope = u32::try_from(parameters.saturating_add(position))
                .map_err(|_cause| CheckRefusal::MachineInvariant)?;
            let closed = gandr_core_term::strengthen_value_type(
                context.arena_mut(),
                field,
                gandr_core_term::Binders::from(scope),
            );
            let Maybe::Present(closed) = closed
            else {
                return Ok(None);
            };
            fields.push(closed.settle(context.arena_mut()));
        }
    }
    Ok(Some(fields))
}
