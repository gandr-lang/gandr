use alloc::collections::BTreeMap;
use alloc::format;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;

use gandr_kernel_term::DeBruijnIndex;
use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::Name;

use super::Arity;
use super::LawFault;
use super::LawNode;
use super::obligation;
use super::read_law;
use crate::arena::ComputationId;
use crate::arena::CoreArena;
use crate::arena::ValueId;
use crate::effect::OperationName;
use crate::rewrite::Binders;
use crate::syntax::ComponentCount;
use crate::syntax::Computation;
use crate::syntax::Value;
use crate::syntax::Zone;

/// State's arities: `get` sends nothing and is replied one value, `put`
/// sends one value and is replied nothing.
///
/// # Specification
/// trivial.
fn state(name: &Name) -> Option<Arity>
{
    let count = ComponentCount::from;
    match name.as_ref() {
        "get" => Some(Arity {
            payload: count(0),
            reply: count(1),
        }),
        "put" => Some(Arity {
            payload: count(1),
            reply: count(0),
        }),
        _ => None,
    }
}

/// Put-get reads over its two metavariables, `s` named first and so the
/// innermost: on the left, `s` at the put, then the get beneath the put's
/// payload binder and its fed value, then `k` applied to the get's binder
/// beneath the get's two; on the right, `k` applied to `s` beneath the put's
/// two (#2272).
#[test]
fn put_get_reads_over_its_metavariables_2272()
{
    // put(s, get(bind t . k(t))) <=> put(s, k(s))
    let left = FreeTerm::op("put", [
        FreeTerm::var("s"),
        FreeTerm::op("get", [FreeTerm::lam(
            "t",
            FreeTerm::inst("k", [FreeTerm::bound("t")]),
        )]),
    ]);
    let right = FreeTerm::op("put", [
        FreeTerm::var("s"),
        FreeTerm::inst("k", [FreeTerm::var("s")]),
    ]);
    let read = read_law((&left, &right), state);
    let Ok(read) = read
    else {
        panic!("put-get reads: {read:?}");
    };
    assert_eq!(read.metavariables, Binders::from(2_u32), "`s` and `k`");
    let operation = |name: &str, depth: u32| LawNode::Operation {
        operation: OperationName::from(name),
        arity: state(&Name::from(name)).unwrap_or_else(|| panic!("State declares `{name}`")),
        depth: Binders::from(depth),
    };
    let carrier = |index: u32, arguments: usize| LawNode::Carrier {
        index: DeBruijnIndex::from(index),
        arguments: ComponentCount::from(arguments),
    };
    let variable = |index: u32| LawNode::Variable(DeBruijnIndex::from(index));
    assert_eq!(
        read.left,
        vec![
            operation("put", 0),
            variable(0),
            operation("get", 2),
            carrier(5, 1),
            variable(0),
        ],
        "the left side in preorder"
    );
    assert_eq!(
        read.right,
        vec![operation("put", 0), variable(0), carrier(3, 1), variable(2)],
        "the right side in preorder"
    );
}

/// A law no handler reads is refused by its fault: an operation the
/// interface does not declare, one without its payload, a continuation that
/// binds no reply where one is due, and a constructor in a payload (#2272).
#[test]
fn a_law_no_handler_reads_is_refused_by_its_fault_2272()
{
    let k = || FreeTerm::var("k");
    let refused = [
        (FreeTerm::op("stop", [k()]), LawFault::Undeclared),
        (FreeTerm::op("put", [k()]), LawFault::Arity),
        (FreeTerm::op("get", [k()]), LawFault::Arity),
        (
            FreeTerm::op("put", [FreeTerm::ctor("Z", []), k()]),
            LawFault::Unread,
        ),
    ];
    for (side, fault) in refused {
        assert_eq!(
            read_law((&side, &k()), state),
            Err(fault),
            "{side:?} is refused as {fault:?}"
        );
    }
}

/// Get-get read through a clause that resumes at a value of the scope's
/// context, `oper get(k) => k(x)` with `x` its innermost: each get applies
/// the clause to the unit, its resumption running the get's continuation at
/// `x` — on the left, `x` raised past the outer get's payload and binder,
/// then `k` at both binders; on the right, `k` at the one binder twice
/// (#2272).
#[test]
fn a_side_resumes_each_clause_through_its_continuation_2272()
{
    let mut arena = CoreArena::new();
    // Beneath the payload's binder, then the stack's: resume(#0, return #2).
    let stack = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let outer = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(2_u32));
    let replied = arena.computation_return(outer);
    let body = arena.computation_resume(stack, replied);
    let clauses = BTreeMap::from([(OperationName::from("get"), body)]);
    // get(bind s . get(bind t . k(s, t))) <=> get(bind s . k(s, s))
    let left = FreeTerm::op("get", [FreeTerm::lam(
        "s",
        FreeTerm::op("get", [FreeTerm::lam(
            "t",
            FreeTerm::inst("k", [FreeTerm::bound("s"), FreeTerm::bound("t")]),
        )]),
    )]);
    let right = FreeTerm::op("get", [FreeTerm::lam(
        "s",
        FreeTerm::inst("k", [FreeTerm::bound("s"), FreeTerm::bound("s")]),
    )]);
    let read = read_law((&left, &right), state);
    let Ok(read) = read
    else {
        panic!("get-get reads: {read:?}");
    };
    let [left, right] = [&read.left, &read.right].map(|side| {
        obligation(&mut arena, (&read, side), &clauses).map(|built| written(&arena, built))
    });
    assert_eq!(
        left.as_deref(),
        Some("(λ. return #2 to (λ. return #4 to force #4 #2 #0) ()) ()"),
        "the left side resumes each get through the next"
    );
    assert_eq!(
        right.as_deref(),
        Some("(λ. return #2 to force #2 #0 #0) ()"),
        "the right side resumes its get once"
    );
    assert_eq!(
        obligation(&mut arena, (&read, &read.left), &BTreeMap::new()),
        None,
        "a side over an operation with no clause builds nothing"
    );
}

/// A part of a side still to be written out.
///
/// # Specification
/// trivial.
enum Part
{
    /// A computation.
    Computation(ComputationId),
    /// A value.
    Value(ValueId),
    /// Text between them.
    Text(&'static str),
}

/// The forms a side is built from, written out: a variable by its index, the
/// unit as `()`, a lambda as `(λ. …)`, an application as its function then
/// its argument, `force` and `return` before what they take, a bind as
/// `… to …`, and any other form as its debug reading.
///
/// # Specification
/// trivial.
fn written(
    arena: &CoreArena,
    id: ComputationId,
) -> String
{
    let mut words: Vec<String> = Vec::new();
    let mut parts = vec![Part::Computation(id)];
    // Each form's parts are pushed last first, so they are written in order.
    while let Some(part) = parts.pop() {
        match part {
            Part::Text(text) => words.push(String::from(text)),
            Part::Value(id) => words.push(match arena.value(id) {
                Some(&Value::Variable { index, .. }) => format!("#{}", u32::from(index)),
                Some(&Value::Tuple(ref components)) if components.is_empty() => String::from("()"),
                Some(other) => format!("{other:?}"),
                None => String::from("?"),
            }),
            Part::Computation(id) => match arena.computation(id) {
                Some(&Computation::Return(value)) => {
                    parts.extend([Part::Value(value), Part::Text("return ")]);
                },
                Some(&Computation::Bind(bound, body)) => {
                    parts.extend([
                        Part::Computation(body),
                        Part::Text(" to "),
                        Part::Computation(bound),
                    ]);
                },
                Some(&Computation::Lambda(body)) => {
                    parts.extend([Part::Text(")"), Part::Computation(body), Part::Text("(λ. ")]);
                },
                Some(&Computation::Application(function, argument)) => {
                    parts.extend([
                        Part::Value(argument),
                        Part::Text(" "),
                        Part::Computation(function),
                    ]);
                },
                Some(&Computation::Force(thunk)) => {
                    parts.extend([Part::Value(thunk), Part::Text("force ")]);
                },
                Some(other) => words.push(format!("{other:?}")),
                None => words.push(String::from("?")),
            },
        }
    }
    words.concat()
}
