//! The guard of a corecursive fixpoint: each call of the fixpoint stands under
//! a constructor of the coinductive datatype it inhabits.
//!
//! A guarded fixpoint `fix s. b` into a coinductive datatype `ν` claims that
//! its body is a coalgebra structure, one constructor of `ν` for each step. The
//! kernel checks the claim in one walk over `b`, and it substitutes nothing.
//! The occurrence of `s` is the call `(force s) a₁ … aₙ`, where `n` is the
//! fixpoint's arity, the count of arrows before the returner of `ν`. No
//! argument `aᵢ` holds `s`. Each path from the root of `b` to a call passes a
//! constructor of `ν`, and each node on that path is one of five:
//!
//! - a constructor of `ν`;
//! - the thunk under a constructor of `ν`;
//! - an abstraction;
//! - a branch of a case whose scrutinee holds no `s`;
//! - a `let` whose bound term holds no `s`.
//!
//! At the value universe the body returns a constructor, so the `return` that
//! holds the constructor is a node of the path too, as the computation that
//! introduces the value.
//!
//! Three things refuse, and no other: a node on the path that is none of the
//! five, an argument of a call that holds `s`, and a bare `s` or `force s`
//! that is no call. A path that reaches a call through no constructor of `ν`
//! breaks the positive condition. A nested fixpoint `fix t. c` is a node of the
//! path: inside `c`, a call of `s` needs a constructor of `ν` on its path from
//! the root of `c`, and the check of `c` walks `t` by the same rule.
//!
//! The syntactic guard is the shadow of the universal property of the final
//! coalgebra. Sized coinduction with copatterns is its general form, where the
//! kernel admits a call whose argument holds the fixpoint at a lower size.
//!
//! # References
//! - `vault:01a156e3-93c7-7e62-9a50-b38b2da60284` — anchor: productivity as a
//!   guard on observations (§ loops-shapes), and the delay type of a partial
//!   program (§ loops-partial), whose `bind` the guard admits.
//! - Thierry Coquand, "Infinite objects in type theory", TYPES 1993.
//! - Andreas Abel and Brigitte Pientka, "Well-founded recursion with copatterns
//!   and sized types", JFP 26 (2016).

use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::CompType;
use gandr_kernel_term::CompTypeId;
use gandr_kernel_term::Computation;
use gandr_kernel_term::ComputationId;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DataFixpoint;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::Reads;
use gandr_kernel_term::StagedPosition;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueType;
use gandr_kernel_term::ValueTypeId;
use quenchant_shape::shape::Maybe;

use crate::env::AdmittedDeclaration;
use crate::env::Entries;
use crate::error::GuardBreak;
use crate::error::GuardNode;
use crate::error::KernelError;

/// Why a guard reads no coinductive datatype at a type.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum NotCoinductive
{
    /// The type is no telescope of arrows into a returner of a nominal datatype
    /// that the environment admits.
    Unnamed,
    /// The datatype is the least fixpoint of its constructors.
    Least,
}

/// What a structural fixpoint descends on.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Descent
{
    /// A coinductive datatype, or a sum that holds one.
    Coinductive,
    /// Any other type.
    Other,
}

/// Whether a node reads the fixpoint's binder.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Reach
{
    /// The node reads the binder.
    Holds,
    /// The node reads no occurrence of the binder.
    Free,
}

/// Why a computation is no call of the fixpoint.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum NotCall
{
    /// The computation is no spine of applications over `force` of the binder.
    Other,
}

/// The arity of a guarded fixpoint and the coinductive datatype it inhabits.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Shape
{
    /// The arrows before the returner.
    arity: usize,
    /// The admission position of the coinductive datatype.
    family: ConstantIndex,
}

/// The coinductive datatype `datatype` applies, by its position.
///
/// # Specification
/// - requires: nothing — a dangling id is admissible input.
/// - ensures: the declaration's position exactly when `datatype` is a nominal
///   datatype application whose admitted declaration is the greatest fixpoint
///   of its constructors.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the delay type answers its position, and the same
///   declaration staged as inductive answers none.
/// - witness: `tests::guard::a_guarded_fixpoint_stands_only_at_a_coinductive_type`
#[spec(ensures: |ret| matches!(ret, Maybe::Absent(_)) || matches!(arena.value_type(datatype), Some(&ValueType::Data { .. })))]
fn coinductive(
    arena: &TermArena,
    entries: &Entries,
    datatype: ValueTypeId,
) -> Maybe<ConstantIndex, NotCoinductive>
{
    let Some(&ValueType::Data { declaration, .. }) = arena.value_type(datatype)
    else {
        return Maybe::Absent(NotCoinductive::Unnamed);
    };
    match entries
        .get(usize::from(declaration))
        .map(AdmittedDeclaration::declaration)
    {
        Some(admitted) if admitted.fixpoint() == DataFixpoint::Greatest => {
            Maybe::Present(declaration)
        },
        Some(_) => Maybe::Absent(NotCoinductive::Least),
        None => Maybe::Absent(NotCoinductive::Unnamed),
    }
}

/// Whether a structural fixpoint at `expected` descends on a coinductive
/// datatype at `position`.
///
/// # Specification
/// - requires: nothing — a dangling id is admissible input.
/// - ensures: [`Descent::Coinductive`] exactly when the arrow at `position` of
///   `expected`'s telescope has a coinductive datatype as its domain, or a sum
///   one of whose summands is one.
/// - provides: the refusal of a fold over a final coalgebra, whose infinite
///   element no structural descent reaches the end of.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// - reason: the loop walks one arrow of the telescope at each step.
/// - measure: the arrows before `position`, each minted before the arrow that
///   holds it.
///
/// # Adequacy
/// - hypothesis: L3 — a structural fixpoint over the delay type is refused, and
///   the same fixpoint over an inductive datatype is admitted.
/// - witness: `tests::guard::a_coinductive_datatype_admits_no_fold`
#[spec(ensures: |ret| ret == Descent::Other || arena.comp_type(expected).is_some())]
pub(super) fn descends_on_coinductive(
    arena: &TermArena,
    entries: &Entries,
    (expected, position): (CompTypeId, StagedPosition),
) -> Descent
{
    let mut cursor = expected;
    let mut passed = 0_usize;
    let domain = loop {
        let (domain, codomain) = match arena.comp_type(cursor) {
            Some(&(CompType::Arrow { domain, codomain } | CompType::Pi { domain, codomain })) => {
                (domain, codomain)
            },
            Some(
                &(CompType::Returner(_)
                | CompType::Returns(_)
                | CompType::With(..)
                | CompType::Element { .. }
                | CompType::Codata { .. }),
            )
            | None => return Descent::Other,
        };
        if passed == usize::from(position) {
            break domain;
        }
        passed = passed.saturating_add(1);
        cursor = codomain;
    };
    let reaches =
        |datatype: ValueTypeId| matches!(coinductive(arena, entries, datatype), Maybe::Present(_));
    let found = match arena.value_type(domain) {
        Some(&ValueType::Sum(ref summands)) => summands.iter().any(|&summand| reaches(summand)),
        Some(_) | None => reaches(domain),
    };
    if found {
        Descent::Coinductive
    }
    else {
        Descent::Other
    }
}

/// The arity of a guarded fixpoint at `expected` and the coinductive datatype
/// it inhabits.
///
/// # Specification
/// - requires: nothing — a dangling id is admissible input.
/// - ensures: the count of arrows before the returner `expected` ends in, and
///   the position of the coinductive datatype the returner returns, exactly
///   when `expected` is a telescope of arrows into a returner of a coinductive
///   datatype.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// - reason: the loop walks one arrow of the telescope at each step.
/// - measure: the arrows of `expected`, each minted before the arrow that holds
///   it.
///
/// # Adequacy
/// - hypothesis: L3 — the stream of ones answers arity zero, the bind of the
///   delay model arity two, and a guarded fixpoint into an inductive datatype
///   answers none.
/// - witness: `tests::guard::a_guarded_fixpoint_stands_only_at_a_coinductive_type`
/// - witness: `tests::guard::the_bind_of_the_delay_model_is_guarded`
#[spec(ensures: |ret| matches!(ret, Maybe::Absent(_)) || arena.comp_type(expected).is_some())]
fn shape(
    arena: &TermArena,
    entries: &Entries,
    expected: CompTypeId,
) -> Maybe<Shape, NotCoinductive>
{
    let mut arity = 0_usize;
    let mut cursor = expected;
    loop {
        match arena.comp_type(cursor) {
            Some(&(CompType::Arrow { codomain, .. } | CompType::Pi { codomain, .. })) => {
                arity = arity.saturating_add(1);
                cursor = codomain;
            },
            Some(&CompType::Returner(result)) => {
                return match coinductive(arena, entries, result) {
                    Maybe::Present(family) => Maybe::Present(Shape { arity, family }),
                    Maybe::Absent(reason) => Maybe::Absent(reason),
                };
            },
            Some(
                &(CompType::Returns(_)
                | CompType::With(..)
                | CompType::Element { .. }
                | CompType::Codata { .. }),
            )
            | None => return Maybe::Absent(NotCoinductive::Unnamed),
        }
    }
}

/// Whether `reads` holds the binder at `depth`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`Reach::Holds`] exactly when the set lists `depth`, or reads
///   every binder.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a call's argument that holds the fixpoint is refused, and
///   one that holds another binder is admitted.
/// - witness: `tests::guard::an_argument_that_holds_the_fixpoint_is_refused`
#[spec(ensures: |ret| (ret == Reach::Holds) == match reads.indices() {
    Maybe::Present(mut indices) => indices.any(|index| index == depth),
    Maybe::Absent(_) => true,
})]
#[inline]
fn holds(
    reads: &Reads,
    depth: DeBruijnIndex,
) -> Reach
{
    let read = match reads.indices() {
        Maybe::Present(mut indices) => indices.any(|index| index == depth),
        Maybe::Absent(_) => true,
    };
    if read { Reach::Holds } else { Reach::Free }
}

/// A call of the fixpoint: how many arguments it applies, and whether one of
/// them holds the fixpoint.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Call
{
    /// The arguments applied to `force s`.
    arguments: usize,
    /// Whether an argument holds `s`.
    held: bool,
}

/// `computation` read as a call of the fixpoint bound at `depth`.
///
/// # Specification
/// - requires: nothing — a dangling id is admissible input.
/// - ensures: a call exactly when `computation` is a spine of applications,
///   possibly empty, over `force` of the variable at `depth`; its count of
///   arguments and whether an argument holds that variable.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// - reason: the loop walks one application of the spine at each step.
/// - measure: the applications of the spine, each minted before the one that
///   holds it.
///
/// # Adequacy
/// - hypothesis: L3 — the stream of ones calls at arity zero, the bind of the
///   delay model at arity two, and a call past the arity is refused.
/// - witness: `tests::guard::the_stream_of_ones_is_guarded`
/// - witness: `tests::guard::a_node_that_is_none_of_the_five_is_refused`
#[spec(ensures: |ret| matches!(ret, Maybe::Absent(_)) || arena.computation(computation).is_some())]
fn call(
    arena: &TermArena,
    computation: ComputationId,
    depth: DeBruijnIndex,
) -> Maybe<Call, NotCall>
{
    let mut cursor = computation;
    let mut found = Call {
        arguments: 0,
        held: false,
    };
    loop {
        let Some(node) = arena.computation(cursor)
        else {
            return Maybe::Absent(NotCall::Other);
        };
        match *node {
            Computation::Application(head, argument) => {
                found.arguments = found.arguments.saturating_add(1);
                found.held =
                    found.held || holds(arena.value_support(argument), depth) == Reach::Holds;
                cursor = head;
            },
            Computation::Force(thunk) => {
                return if matches!(arena.value(thunk), Some(&Value::Variable(index)) if index == depth)
                {
                    Maybe::Present(found)
                }
                else {
                    Maybe::Absent(NotCall::Other)
                };
            },
            Computation::DataCase { .. }
            | Computation::RecordProjection(..)
            | Computation::TupleProjection(..)
            | Computation::Lambda(_)
            | Computation::Return(_)
            | Computation::Bind(..)
            | Computation::ReturnAll(_)
            | Computation::BindAll { .. }
            | Computation::Case { .. }
            | Computation::SigmaSplit { .. }
            | Computation::ListFold { .. }
            | Computation::ListCase { .. }
            | Computation::Transport(..)
            | Computation::PathTransport { .. }
            | Computation::TelescopeTransport { .. }
            | Computation::Ride { .. }
            | Computation::TelescopeRide { .. }
            | Computation::RelatedApplication { .. }
            | Computation::With(_)
            | Computation::Project(..)
            | Computation::Fixpoint { .. } => return Maybe::Absent(NotCall::Other),
        }
    }
}

/// A node of the body the walk visits.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Node
{
    /// A computation.
    Computation(ComputationId),
    /// A value.
    Value(ValueId),
}

/// Where a node stands relative to the constructors of the coinductive type.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Place
{
    /// A field of a constructor of the coinductive type.
    Field,
    /// Anywhere else.
    Elsewhere,
}

/// One node of the walk: the node, the depth the fixpoint's binder stands at,
/// whether a constructor of the coinductive type stands above it, and where it
/// stands.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Step
{
    /// The node.
    node: Node,
    /// The de Bruijn index of the fixpoint's binder at the node.
    depth: DeBruijnIndex,
    /// Whether the path to the node passes a constructor of the coinductive
    /// type.
    guarded: bool,
    /// Where the node stands.
    place: Place,
}

/// Check the guard of the fixpoint `fix s. body` at `expected`.
///
/// # Specification
/// - requires: `body` is checked under the self binder at index zero.
/// - ensures: success exactly when `expected` is a telescope of arrows into a
///   returner of a coinductive datatype `ν`, and each path from the root of
///   `body` to a call of `s` at the telescope's arity passes a constructor of
///   `ν` through the five nodes the guard admits, every argument of the call
///   free of `s`, and `s` stands nowhere else.
/// - provides: the guard of corecursion as a claim the kernel checks: one walk,
///   no substitution, no node minted.
/// - fails: [`KernelError::GuardedNotCoinductive`] for any other `expected`;
///   [`KernelError::Unguarded`] naming the first break the walk meets.
/// - panics: none.
///
/// # Errors
/// As `- fails:`, and [`KernelError::ArenaFault`] for an unreadable node.
///
/// # Clause cost
/// - bound: one visit for each distinct node, depth and place the walk reaches
///   on a path that holds `s`; a node that holds no `s` ends its path.
///
/// # Termination
/// - reason: the `while let` loop over an explicit worklist, and a visited set
///   that admits each step once.
/// - measure: the steps not yet visited, finite because each child is minted
///   before its parent.
///
/// # Adequacy
/// - hypothesis: L3 — the stream of ones, the bind of the delay model and a
///   nested fixpoint are admitted; a case on the call, an argument that holds
///   the fixpoint, a bare fixpoint, a call through no constructor and a `let`
///   that binds the fixpoint are each refused by name.
/// - witness: `tests::guard::the_stream_of_ones_is_guarded`
/// - witness: `tests::guard::the_bind_of_the_delay_model_is_guarded`
/// - witness: `tests::guard::a_nested_fixpoint_checks_as_two_walks`
/// - witness: `tests::guard::a_node_that_is_none_of_the_five_is_refused`
/// - witness: `tests::guard::an_argument_that_holds_the_fixpoint_is_refused`
/// - witness: `tests::guard::a_fixpoint_that_is_no_call_is_refused`
/// - witness: `tests::guard::a_let_is_transparent_unless_it_binds_the_fixpoint`
#[spec(ensures: |ret| ret.is_err() || matches!(shape(arena, entries, expected), Maybe::Present(_)))]
pub(super) fn guarded(
    arena: &TermArena,
    entries: &Entries,
    (expected, body): (CompTypeId, ComputationId),
) -> Result<(), KernelError>
{
    let Maybe::Present(Shape { arity, family }) = shape(arena, entries, expected)
    else {
        return Err(KernelError::GuardedNotCoinductive);
    };
    let refuse = |at: GuardBreak| Err(KernelError::Unguarded(at));
    let mut pending = Vec::from([Step {
        node: Node::Computation(body),
        depth: DeBruijnIndex::from(0_u32),
        guarded: false,
        place: Place::Elsewhere,
    }]);
    let mut visited = BTreeSet::new();
    while let Some(step) = pending.pop() {
        if !visited.insert(step) {
            continue;
        }
        let Step {
            node,
            depth,
            guarded,
            place,
        } = step;
        let inner = DeBruijnIndex::from(u32::from(depth).saturating_add(1));
        match node {
            Node::Computation(id) => {
                if holds(arena.computation_support(id), depth) == Reach::Free {
                    continue;
                }
                if let Maybe::Present(found) = call(arena, id, depth) {
                    if found.held {
                        return refuse(GuardBreak::Argument);
                    }
                    if found.arguments > arity {
                        return refuse(GuardBreak::Node(GuardNode::Application));
                    }
                    if found.arguments < arity {
                        return refuse(GuardBreak::Bare);
                    }
                    if !guarded {
                        return refuse(GuardBreak::Unconstructed);
                    }
                    continue;
                }
                let child = |inside: ComputationId, depth: DeBruijnIndex, guarded: bool| Step {
                    node: Node::Computation(inside),
                    depth,
                    guarded,
                    place: Place::Elsewhere,
                };
                match *arena.computation(id).ok_or(KernelError::ArenaFault)? {
                    Computation::Lambda(inside) => pending.push(child(inside, inner, guarded)),
                    Computation::Case {
                        scrutinee,
                        ref branches,
                    } => {
                        if holds(arena.value_support(scrutinee), depth) == Reach::Holds {
                            return refuse(GuardBreak::Node(GuardNode::Case));
                        }
                        for &branch in branches {
                            pending.push(child(branch, inner, guarded));
                        }
                    },
                    Computation::DataCase {
                        scrutinee,
                        motive,
                        ref branches,
                        ..
                    } => {
                        if holds(arena.value_support(scrutinee), depth) == Reach::Holds
                            || holds(arena.comp_type_support(motive), inner) == Reach::Holds
                        {
                            return refuse(GuardBreak::Node(GuardNode::Case));
                        }
                        for &branch in branches {
                            pending.push(child(branch, depth, guarded));
                        }
                    },
                    Computation::Bind(bound, continued) => {
                        if holds(arena.computation_support(bound), depth) == Reach::Holds {
                            return refuse(GuardBreak::Node(GuardNode::Let));
                        }
                        pending.push(child(continued, inner, guarded));
                    },
                    Computation::BindAll {
                        bound,
                        arity: count,
                        body: continued,
                    } => {
                        if holds(arena.computation_support(bound), depth) == Reach::Holds {
                            return refuse(GuardBreak::Node(GuardNode::Let));
                        }
                        let binders = u32::try_from(usize::from(count)).unwrap_or(u32::MAX);
                        let below = DeBruijnIndex::from(u32::from(depth).saturating_add(binders));
                        pending.push(child(continued, below, guarded));
                    },
                    Computation::Return(value) => pending.push(Step {
                        node: Node::Value(value),
                        depth,
                        guarded,
                        place: Place::Elsewhere,
                    }),
                    // The constructors outside a nested fixpoint do not count
                    // inside it.
                    Computation::Fixpoint { body: inside, .. } => {
                        pending.push(child(inside, inner, false));
                    },
                    Computation::Application(_, argument) => {
                        return refuse(
                            if matches!(arena.value(argument), Some(&Value::Variable(index)) if index == depth)
                            {
                                GuardBreak::Bare
                            }
                            else {
                                GuardBreak::Node(GuardNode::Application)
                            },
                        );
                    },
                    Computation::Force(thunk) => {
                        return refuse(
                            if matches!(arena.value(thunk), Some(&Value::Variable(index)) if index == depth)
                            {
                                GuardBreak::Bare
                            }
                            else {
                                GuardBreak::Node(GuardNode::Other)
                            },
                        );
                    },
                    Computation::RecordProjection(..)
                    | Computation::TupleProjection(..)
                    | Computation::Project(..) => {
                        return refuse(GuardBreak::Node(GuardNode::Projection));
                    },
                    Computation::SigmaSplit { .. }
                    | Computation::ListFold { .. }
                    | Computation::ListCase { .. } => {
                        return refuse(GuardBreak::Node(GuardNode::Case));
                    },
                    Computation::ReturnAll(_)
                    | Computation::Transport(..)
                    | Computation::PathTransport { .. }
                    | Computation::TelescopeTransport { .. }
                    | Computation::Ride { .. }
                    | Computation::TelescopeRide { .. }
                    | Computation::RelatedApplication { .. }
                    | Computation::With(_) => return refuse(GuardBreak::Node(GuardNode::Other)),
                }
            },
            Node::Value(id) => {
                if holds(arena.value_support(id), depth) == Reach::Free {
                    continue;
                }
                match *arena.value(id).ok_or(KernelError::ArenaFault)? {
                    Value::Variable(_) => return refuse(GuardBreak::Bare),
                    Value::Constructor {
                        family: owner,
                        ref fields,
                        ..
                    } if owner == family => {
                        for &field in fields {
                            pending.push(Step {
                                node: Node::Value(field),
                                depth,
                                guarded: true,
                                place: Place::Field,
                            });
                        }
                    },
                    Value::Constructor { .. } => {
                        return refuse(GuardBreak::Node(GuardNode::Constructor));
                    },
                    Value::Thunk(inside) if place == Place::Field => pending.push(Step {
                        node: Node::Computation(inside),
                        depth,
                        guarded,
                        place: Place::Elsewhere,
                    }),
                    Value::Thunk(_) => return refuse(GuardBreak::Node(GuardNode::Thunk)),
                    Value::Record(_)
                    | Value::Restrict { .. }
                    | Value::SessionPath { .. }
                    | Value::SessionFlow { .. }
                    | Value::Stay { .. }
                    | Value::ForwardFlow { .. }
                    | Value::FunctionFlow { .. }
                    | Value::Then { .. }
                    | Value::FlowProduct(..)
                    | Value::PathRefl(_)
                    | Value::PathProduct(..)
                    | Value::PathEquiv { .. }
                    | Value::Univalence(_)
                    | Value::Here { .. }
                    | Value::Returned(_)
                    | Value::Higher { .. }
                    | Value::HigherEvaluation { .. }
                    | Value::QuantifiedEvaluation { .. }
                    | Value::Constant(_)
                    | Value::Literal(_)
                    | Value::Tuple(_)
                    | Value::Injection(..)
                    | Value::ListNil
                    | Value::ListCons(..)
                    | Value::Lift { .. }
                    | Value::Quote(_)
                    | Value::QuoteComputation(_)
                    | Value::StaticApplication(..) => {
                        return refuse(GuardBreak::Node(GuardNode::Other));
                    },
                }
            },
        }
    }
    Ok(())
}
