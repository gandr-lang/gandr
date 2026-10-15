//! Replaying a fixpoint's structural-descent claim, mirroring the kernel's.
//!
//! The claim says the fixpoint is `fix x. λy. case y [C] of { c_i ↦ λf̄_i.
//! N_i }` at a function out of a nominal data application, each branch
//! opening exactly its constructor's fields, and every occurrence of `x` a
//! call `(force x) a` whose argument is a field of the scrutinised
//! constructor or the value a function field returns — the `t` of
//! `t ← (force f) ȳ`. The walk replays it over one explicit stack; it
//! searches for nothing, and the kernel replays the same claim on its own.
//!
//! A fixpoint checks against any computation type `C`, its body checked at `C`
//! under a binder of `U C`; in synthesis position it is refused, naming the
//! form. A structural-descent claim is replayed by this walk before the body is
//! checked. A claim that fails is `DescentNotReplayed`, naming the fixpoint and
//! the kernel's `DescentRefusal`, and readmission re-derives the same verdict.
//! A partial fixpoint carries no claim and is checked at any computation type.
//! Witnesses:
//! `recursive_data::recursive_data::descent_claims_replay_or_are_refused_by_name`
//! and
//! `recursive_data::recursive_data::a_fixpoint_checks_at_every_computation_type`.

use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Binders;
use gandr_core_term::CompType;
use gandr_core_term::CompTypeId;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::SplitMotive;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::Zone;
use gandr_core_term::control::StackFrame;
use gandr_kernel_term::DescentRefusal;
use quenchant_shape::shape::Maybe;

use crate::CheckRefusal;
use crate::CheckingContext;
use crate::occurrence::AnyNode;
use crate::view::ValueTypeView;
use crate::view::value_type_view;

/// The binder level of the fixpoint's self reference, counted from the
/// fixpoint's body.
const SELF_LEVEL: u32 = 0;

/// The binder level of the scrutinised argument.
const ARGUMENT_LEVEL: u32 = 1;

/// The binder level of the first field, past the self binder and the
/// scrutinised argument's binder.
const FIRST_FIELD: u32 = 2;

quenchant_shape::reason_enum! {
    /// Why a value names no binder level inside the fixpoint.
    mod variable_level {
        /// The value is no variable bound inside the fixpoint.
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        pub enum Absent {
            /// The value is not an intuitionistic variable.
            NotVariable,
            /// The variable is bound outside the fixpoint.
            Outside,
        }
    }
}

/// The levels a self call may descend to beyond the branch's fields: the
/// results bound from forcing a function field, as a persistent list.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Results
{
    /// No function field's result is bound here.
    Empty,
    /// The link at this position of the result table is the innermost.
    At(ResultLink),
}

/// A position in a branch's result table.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ResultLink(usize);

/// One bound function-field result and the results bound outside it.
#[derive(Clone, Copy, Debug)]
struct Link
{
    /// The binder level of the result.
    level: Binders,
    /// The results bound outside it.
    outer: Results,
}

/// Whether a level is one a self call may descend to.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Descent
{
    /// A field of the scrutinised constructor or a function field's result.
    Smaller,
    /// Anything else.
    Unrelated,
}

/// The fixed half of a branch walk: its field levels and the result table.
struct Branch
{
    /// One past the last field level.
    fields_end: Binders,
    /// Every bound function-field result, linked innermost to outermost.
    links: Vec<Link>,
}

impl Branch
{
    /// Whether `level` is a field of the scrutinised constructor or a
    /// function field's result in scope at `results`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Smaller` exactly when `level` lies in the branch's field
    ///   range or is linked from `results`.
    /// - panics: none.
    ///
    /// # Termination
    /// - reason: the `while let` loop follows outer links, each strictly
    ///   earlier in the table, not recursion.
    /// - measure: the position of the current link.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a call at a field and at a function field's result
    ///   replays; a call at the scrutinee does not.
    /// - witness: `recursive_data::recursive_data::descent_claims_replay_or_are_refused_by_name`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body follows the result chain through one branch's link table; the check scans that table once"
        )
    )]
    #[spec(ensures: |ret| ret == Descent::Unrelated
        || (FIRST_FIELD .. u32::from(self.fields_end)).contains(&u32::from(level))
        || self.links.iter().any(|link| link.level == level))]
    fn descent(
        &self,
        level: Binders,
        results: Results,
    ) -> Descent
    {
        if (FIRST_FIELD .. u32::from(self.fields_end)).contains(&u32::from(level)) {
            return Descent::Smaller;
        }
        let mut cursor = results;
        while let Results::At(ResultLink(position)) = cursor {
            let Some(link) = self.links.get(position)
            else {
                return Descent::Unrelated;
            };
            if link.level == level {
                return Descent::Smaller;
            }
            cursor = link.outer;
        }
        Descent::Unrelated
    }
}

/// The binder level a value names from under `depth` binders, counted from
/// the fixpoint's body.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the level `depth - 1 - d` for an intuitionistic variable at
///   distance `d`, when that is non-negative.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the self variable is recognised at every depth the
///   derived eliminator's calls stand at, and a variable bound outside the
///   fixpoint is never mistaken for it.
/// - witness: `recursive_data::recursive_data::descent_claims_replay_or_are_refused_by_name`
#[spec(ensures: |ret| matches!(ret, Maybe::Present(found) if u32::from(found) < u32::from(depth)) || matches!(ret, Maybe::Absent(_)))]
fn variable_level(
    arena: &CoreArena,
    value: ValueId,
    depth: Binders,
) -> Maybe<Binders, variable_level::Absent>
{
    let Some(&Value::Variable {
        zone: Zone::Intuitionistic,
        index,
    }) = arena.value(value)
    else {
        return Maybe::Absent(variable_level::Absent::NotVariable);
    };
    u32::from(depth)
        .checked_sub(u32::from(index))
        .and_then(|outer| outer.checked_sub(1))
        .map_or(Maybe::Absent(variable_level::Absent::Outside), |level| {
            Maybe::Present(Binders::from(level))
        })
}

/// Whether `bound` is `(force f) ȳ` for a field or function-field result
/// `f`: what it returns is a smaller value a self call may descend to.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `Smaller` exactly when `bound` is at least one application over
///   the force of a variable whose level descends.
/// - panics: none.
///
/// # Termination
/// - reason: the `while let` loop descends application heads, not recursion.
/// - measure: the head's arena position.
///
/// # Adequacy
/// - hypothesis: L3 — a function field's hypothesis replays through the bind it
///   introduces.
/// - witness: `recursive_data::recursive_data::descent_claims_replay_or_are_refused_by_name`
#[spec(ensures: |ret| ret == Descent::Unrelated || matches!(arena.computation(bound), Some(&Computation::Application(..))))]
fn forced_field(
    arena: &CoreArena,
    branch: &Branch,
    bound: ComputationId,
    depth: Binders,
    results: Results,
) -> Descent
{
    let mut focus = bound;
    let mut applications = 0_usize;
    while let Some(&Computation::Application(head, _)) = arena.computation(focus) {
        applications = applications.saturating_add(1);
        focus = head;
    }
    if applications == 0 {
        return Descent::Unrelated;
    }
    let Some(&Computation::Force(forced)) = arena.computation(focus)
    else {
        return Descent::Unrelated;
    };
    match variable_level(arena, forced, depth) {
        Maybe::Present(level) if u32::from(level) != SELF_LEVEL => branch.descent(level, results),
        Maybe::Present(_) | Maybe::Absent(_) => Descent::Unrelated,
    }
}

/// Whether a value is the fixpoint's self variable.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Reference
{
    /// The self variable.
    ToSelf,
    /// Anything else.
    Other,
}

/// Whether the value at `id`, under `depth` binders, is the self variable.
///
/// # Specification
/// trivial.
fn reference(
    arena: &CoreArena,
    id: ValueId,
    depth: Binders,
) -> Reference
{
    match variable_level(arena, id, depth) {
        Maybe::Present(level) if u32::from(level) == SELF_LEVEL => Reference::ToSelf,
        Maybe::Present(_) | Maybe::Absent(_) => Reference::Other,
    }
}

/// Walk one branch body, or the motive, for unguarded or non-descending
/// self references.
///
/// # Specification
/// - requires: `root` stands under `depth` binders counted from the fixpoint's
///   body, and `branch` names its field levels.
/// - ensures: success exactly when every occurrence of the self variable is the
///   head of a call whose argument is a field, a function field's result in
///   scope, or a call of a function field written in place, nested or run.
/// - fails: the first unguarded or non-descending occurrence the walk meets.
/// - panics: none.
///
/// # Errors
/// `UnguardedSelfReference` or `NonDescendingCall`.
///
/// # Termination
/// - reason: the `while let` worklist, not recursion.
/// - measure: the nodes left below the root along each path, finite because the
///   arena is acyclic.
///
/// # Adequacy
/// - hypothesis: L3 — a call at a field, at a function field's result, at a
///   function field's call written in place and under a nested binder replays;
///   a call at the scrutinee itself and a bare forced self reference refuse.
/// - witness: `recursive_data::recursive_data::descent_claims_replay_or_are_refused_by_name`
#[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(DescentRefusal::UnguardedSelfReference | DescentRefusal::NonDescendingCall)))]
fn walk(
    arena: &CoreArena,
    branch: &mut Branch,
    root: AnyNode,
    depth: Binders,
) -> Result<(), DescentRefusal>
{
    let mut pending: Vec<(AnyNode, Binders, Results)> = Vec::from([(root, depth, Results::Empty)]);
    while let Some((node, depth, results)) = pending.pop() {
        let deeper = depth.deeper();
        match node {
            AnyNode::Value(id) => {
                match arena.value(id) {
                    Some(&Value::Variable { .. }) => {
                        if reference(arena, id, depth) == Reference::ToSelf {
                            return Err(DescentRefusal::UnguardedSelfReference);
                        }
                    },
                    Some(&Value::Constructor {
                        datatype,
                        ref fields,
                        ..
                    }) => {
                        pending.push((AnyNode::ValueType(datatype), depth, results));
                        pending.extend(
                            fields
                                .iter()
                                .map(|&field| (AnyNode::Value(field), depth, results)),
                        );
                    },
                    Some(&Value::Record(ref fields)) => {
                        pending.extend(
                            fields
                                .values()
                                .map(|&field| (AnyNode::Value(field), depth, results)),
                        );
                    },
                    Some(&Value::PathEquiv {
                        path_type,
                        forward,
                        backward,
                        ..
                    }) => {
                        pending.push((AnyNode::ValueType(path_type), depth, results));
                        pending.push((AnyNode::Value(forward), depth, results));
                        pending.push((AnyNode::Value(backward), depth, results));
                    },
                    Some(&Value::Tuple(ref components)) => {
                        pending.extend(
                            components
                                .iter()
                                .map(|&component| (AnyNode::Value(component), depth, results)),
                        );
                    },
                    Some(&Value::Recorded(ref moves)) => {
                        pending.extend(moves.iter().filter_map(
                            |movement| match movement.payload() {
                                Maybe::Present(payload) => {
                                    Some((AnyNode::Value(payload), depth, results))
                                },
                                Maybe::Absent(_) => None,
                            },
                        ));
                    },
                    Some(
                        &(Value::PathProduct(first, second)
                        | Value::Funext(first, second)
                        | Value::Equiv(first, second)
                        | Value::Then(first, second)
                        | Value::FlowProduct(first, second)
                        | Value::FunctionFlow(first, second)
                        | Value::SessionRelated {
                            source: first,
                            target: second,
                            ..
                        }
                        | Value::Ua {
                            forward: first,
                            backward: second,
                            ..
                        }
                        | Value::ListCons(first, second)
                        | Value::StaticApplication(first, second)),
                    ) => {
                        pending.push((AnyNode::Value(first), depth, results));
                        pending.push((AnyNode::Value(second), depth, results));
                    },
                    Some(&Value::Reify(ref frames)) => {
                        for frame in frames.iter() {
                            match *frame {
                                StackFrame::Apply(value) => {
                                    pending.push((AnyNode::Value(value), depth, results));
                                },
                                StackFrame::Bind(body) => {
                                    pending.push((AnyNode::Computation(body), deeper, results));
                                },
                                StackFrame::Project(_) => {},
                            }
                        }
                    },
                    Some(
                        &(Value::PathRefl(body)
                        | Value::Here(body)
                        | Value::Stay(body)
                        | Value::Forward(body)
                        | Value::Injection(_, body)
                        | Value::Lift { body, .. }
                        | Value::Mark { body, .. }),
                    ) => {
                        pending.push((AnyNode::Value(body), depth, results));
                    },
                    Some(&Value::StaticLambda(body)) => {
                        pending.push((AnyNode::Value(body), deeper, results));
                    },
                    Some(
                        &(Value::Thunk(body)
                        | Value::Returned(body)
                        | Value::Nested(body)
                        | Value::Run(body)),
                    ) => {
                        pending.push((AnyNode::Computation(body), depth, results));
                    },
                    Some(&Value::Quote(quoted)) => {
                        pending.push((AnyNode::ValueType(quoted), depth, results));
                    },
                    Some(&Value::QuoteComputation(quoted)) => {
                        pending.push((AnyNode::CompType(quoted), depth, results));
                    },
                    Some(
                        &(Value::Primitive { .. }
                        | Value::Constant(_)
                        | Value::ListNil
                        | Value::Literal(_)
                        | Value::Hole(_)),
                    )
                    | None => {},
                }
            },
            AnyNode::Computation(id) => match arena.computation(id) {
                Some(&Computation::Application(head, argument)) => {
                    let call = matches!(arena.computation(head), Some(&Computation::Force(forced))
                        if reference(arena, forced, depth) == Reference::ToSelf);
                    if call {
                        let descends = match variable_level(arena, argument, depth) {
                            Maybe::Present(level) => branch.descent(level, results),
                            // A function field's result written in place
                            // descends as the variable its elaborated bind
                            // binds does.
                            Maybe::Absent(_) => match arena.value(argument) {
                                Some(&(Value::Nested(nested) | Value::Run(nested))) => {
                                    pending.push((AnyNode::Computation(nested), depth, results));
                                    forced_field(arena, branch, nested, depth, results)
                                },
                                Some(_) | None => Descent::Unrelated,
                            },
                        };
                        if descends == Descent::Unrelated {
                            return Err(DescentRefusal::NonDescendingCall);
                        }
                    }
                    else {
                        pending.push((AnyNode::Computation(head), depth, results));
                        pending.push((AnyNode::Value(argument), depth, results));
                    }
                },
                Some(&Computation::Bind(bound, body)) => {
                    let inner = match forced_field(arena, branch, bound, depth, results) {
                        Descent::Smaller => {
                            let position = ResultLink(branch.links.len());
                            branch.links.push(Link {
                                level: depth,
                                outer: results,
                            });
                            Results::At(position)
                        },
                        Descent::Unrelated => results,
                    };
                    pending.push((AnyNode::Computation(bound), depth, results));
                    pending.push((AnyNode::Computation(body), deeper, inner));
                },
                Some(&Computation::DataCase {
                    scrutinee,
                    motive,
                    ref branches,
                }) => {
                    pending.push((AnyNode::Value(scrutinee), depth, results));
                    pending.push((AnyNode::CompType(motive), deeper, results));
                    pending.extend(
                        branches
                            .iter()
                            .map(|&case| (AnyNode::Computation(case), depth, results)),
                    );
                },
                Some(&Computation::Case {
                    scrutinee,
                    ref branches,
                }) => {
                    pending.push((AnyNode::Value(scrutinee), depth, results));
                    pending.extend(
                        branches
                            .iter()
                            .map(|&branch| (AnyNode::Computation(branch), deeper, results)),
                    );
                },
                Some(
                    &(Computation::Lambda(body)
                    | Computation::Fixpoint { body, .. }
                    | Computation::Shift(body)),
                ) => {
                    pending.push((AnyNode::Computation(body), deeper, results));
                },
                Some(
                    &(Computation::Mark { body, .. }
                    | Computation::Reset(body)
                    | Computation::Project(_, body)),
                ) => {
                    pending.push((AnyNode::Computation(body), depth, results));
                },
                Some(&Computation::With(first, second)) => {
                    pending.push((AnyNode::Computation(first), depth, results));
                    pending.push((AnyNode::Computation(second), depth, results));
                },
                Some(&Computation::Resume(stack, body)) => {
                    pending.push((AnyNode::Value(stack), depth, results));
                    pending.push((AnyNode::Computation(body), depth, results));
                },
                // Components bind unrelated: a call on one is refused, never
                // accepted on a descent the kernel's projections might not see.
                Some(&Computation::Split {
                    scrutinee,
                    arity,
                    motive,
                    body,
                }) => {
                    let inside = (0_usize .. usize::from(arity)).fold(depth, |at, _| at.deeper());
                    pending.push((AnyNode::Value(scrutinee), depth, results));
                    if let SplitMotive::Scrutinee(motive) = motive {
                        pending.push((AnyNode::CompType(motive), deeper, results));
                    }
                    pending.push((AnyNode::Computation(body), inside, results));
                },
                Some(&Computation::Perform {
                    ref signature,
                    payload,
                    ..
                }) => {
                    pending.push((AnyNode::Value(payload), depth, results));
                    pending.extend(
                        signature
                            .types()
                            .map(|operation| (AnyNode::ValueType(operation), depth, results)),
                    );
                },
                Some(&Computation::Exercise {
                    capability,
                    ref signature,
                    payload,
                    ..
                }) => {
                    pending.push((AnyNode::Value(capability), depth, results));
                    pending.push((AnyNode::Value(payload), depth, results));
                    pending.extend(
                        signature
                            .types()
                            .map(|operation| (AnyNode::ValueType(operation), depth, results)),
                    );
                },
                Some(&Computation::Scope {
                    ref signature,
                    subject,
                    on_return,
                    ref clauses,
                }) => {
                    pending.push((AnyNode::Computation(subject), deeper, results));
                    pending.push((AnyNode::Computation(on_return), deeper, results));
                    pending.extend(clauses.iter().map(|clause| {
                        (AnyNode::Computation(clause.body), deeper.deeper(), results)
                    }));
                    pending.extend(
                        signature
                            .types()
                            .map(|operation| (AnyNode::ValueType(operation), depth, results)),
                    );
                },
                Some(&Computation::Handle {
                    ref signature,
                    subject,
                    on_return,
                    ref clauses,
                }) => {
                    pending.push((AnyNode::Computation(subject), depth, results));
                    pending.push((AnyNode::Computation(on_return), deeper, results));
                    pending.extend(clauses.iter().map(|clause| {
                        (AnyNode::Computation(clause.body), deeper.deeper(), results)
                    }));
                    pending.extend(
                        signature
                            .types()
                            .map(|operation| (AnyNode::ValueType(operation), depth, results)),
                    );
                },
                Some(&Computation::ListFold {
                    element,
                    result,
                    list,
                    on_nil,
                    on_cons,
                }) => {
                    pending.push((AnyNode::ValueType(element), depth, results));
                    pending.push((AnyNode::ValueType(result), depth, results));
                    pending.push((AnyNode::Value(list), depth, results));
                    pending.push((AnyNode::Computation(on_nil), depth, results));
                    pending.push((AnyNode::Computation(on_cons), deeper.deeper(), results));
                },
                Some(&Computation::Primitive { ref arguments, .. }) => {
                    pending.extend(
                        arguments
                            .iter()
                            .map(|&argument| (AnyNode::Value(argument), depth, results)),
                    );
                },
                Some(
                    &(Computation::RecordProjection(value, _)
                    | Computation::TupleProjection(value, _)
                    | Computation::Return(value)
                    | Computation::Force(value)),
                ) => {
                    pending.push((AnyNode::Value(value), depth, results));
                },
                Some(&Computation::Transport(path, value)) => {
                    pending.push((AnyNode::Value(path), depth, results));
                    pending.push((AnyNode::Value(value), depth, results));
                },
                Some(
                    &(Computation::PathTransport {
                        motive,
                        path,
                        value,
                    }
                    | Computation::Ride {
                        motive,
                        flow: path,
                        value,
                    }),
                ) => {
                    pending.push((AnyNode::ValueType(motive), deeper, results));
                    pending.push((AnyNode::Value(path), depth, results));
                    pending.push((AnyNode::Value(value), depth, results));
                },
                // The motive's arrows bind the telescope themselves.
                Some(&Computation::TelescopeTransport {
                    motive,
                    path,
                    start,
                    over,
                    value,
                }) => {
                    pending.push((AnyNode::CompType(motive), depth, results));
                    pending.extend(
                        [path, start, over, value]
                            .map(|child| (AnyNode::Value(child), depth, results)),
                    );
                },
                // A fork binds linearly; the intuitionistic depth stays.
                Some(&Computation::Session(ref action)) => {
                    pending.extend(
                        action
                            .values()
                            .map(|value| (AnyNode::Value(value), depth, results)),
                    );
                    pending.extend(
                        action
                            .value_types()
                            .map(|ty| (AnyNode::ValueType(ty), depth, results)),
                    );
                    pending.extend(
                        action
                            .computations()
                            .map(|child| (AnyNode::Computation(child), depth, results)),
                    );
                },
                Some(&Computation::Hole(_)) | None => {},
            },
            AnyNode::ValueType(id) => match arena.value_type(id) {
                Some(&ValueType::Data { ref arguments, .. }) => {
                    pending.extend(
                        arguments
                            .iter()
                            .map(|&argument| (AnyNode::Value(argument), depth, results)),
                    );
                },
                Some(&ValueType::Record(ref fields)) => {
                    pending.extend(
                        fields
                            .values()
                            .map(|&field| (AnyNode::ValueType(field), depth, results)),
                    );
                },
                Some(&(ValueType::Product(ref parts) | ValueType::Sum(ref parts))) => {
                    pending.extend(
                        parts
                            .iter()
                            .map(|&part| (AnyNode::ValueType(part), depth, results)),
                    );
                },
                Some(&ValueType::Session(ref session)) => {
                    pending.extend(
                        session
                            .payloads()
                            .iter()
                            .map(|&payload| (AnyNode::ValueType(payload), depth, results)),
                    );
                },
                Some(&ValueType::StaticPi {
                    domain: first,
                    codomain: second,
                }) => {
                    pending.push((AnyNode::ValueType(first), depth, results));
                    pending.push((AnyNode::ValueType(second), depth, results));
                },
                Some(&ValueType::Sigma { first, second }) => {
                    pending.push((AnyNode::ValueType(first), depth, results));
                    pending.push((AnyNode::ValueType(second), deeper, results));
                },
                Some(&ValueType::PathUniverse(source, target)) => {
                    pending.push((AnyNode::Value(source), depth, results));
                    pending.push((AnyNode::Value(target), depth, results));
                },
                Some(&ValueType::Path {
                    carrier,
                    left,
                    right,
                }) => {
                    pending.push((AnyNode::ValueType(carrier), depth, results));
                    pending.push((AnyNode::Value(left), depth, results));
                    pending.push((AnyNode::Value(right), depth, results));
                },
                Some(&ValueType::Flow {
                    carrier,
                    source,
                    target,
                }) => {
                    pending.push((AnyNode::ValueType(carrier), depth, results));
                    pending.push((AnyNode::Value(source), depth, results));
                    pending.push((AnyNode::Value(target), depth, results));
                },
                Some(&ValueType::Run(session)) => {
                    pending.push((AnyNode::Value(session), depth, results));
                },
                Some(&ValueType::Thunk(body)) => {
                    pending.push((AnyNode::CompType(body), depth, results));
                },
                Some(&ValueType::List(element)) => {
                    pending.push((AnyNode::ValueType(element), depth, results));
                },
                Some(&ValueType::Stack { input, output }) => {
                    pending.push((AnyNode::CompType(input), depth, results));
                    pending.push((AnyNode::CompType(output), depth, results));
                },
                Some(&ValueType::Lift { inner, .. }) => {
                    pending.push((AnyNode::ValueType(inner), depth, results));
                },
                Some(&ValueType::Element { code, .. }) => {
                    pending.push((AnyNode::Value(code), depth, results));
                },
                Some(&ValueType::Capability { ref authority, .. }) => {
                    pending.extend(
                        authority
                            .types()
                            .map(|operation| (AnyNode::ValueType(operation), depth, results)),
                    );
                },
                Some(
                    &(ValueType::Base(_)
                    | ValueType::Universe { .. }
                    | ValueType::Abstract(_)
                    | ValueType::Unknown),
                )
                | None => {},
            },
            AnyNode::CompType(id) => match arena.comp_type(id) {
                Some(&CompType::Returner {
                    result,
                    ref effects,
                }) => {
                    pending.push((AnyNode::ValueType(result), depth, results));
                    pending.extend(
                        effects
                            .types()
                            .map(|operation| (AnyNode::ValueType(operation), depth, results)),
                    );
                },
                Some(&CompType::With(first, second)) => {
                    pending.push((AnyNode::CompType(first), depth, results));
                    pending.push((AnyNode::CompType(second), depth, results));
                },
                Some(&CompType::Arrow { domain, codomain }) => {
                    pending.push((AnyNode::ValueType(domain), depth, results));
                    pending.push((AnyNode::CompType(codomain), depth, results));
                },
                Some(&CompType::Pi { domain, codomain }) => {
                    pending.push((AnyNode::ValueType(domain), depth, results));
                    pending.push((AnyNode::CompType(codomain), deeper, results));
                },
                Some(&CompType::Element { code, .. }) => {
                    pending.push((AnyNode::Value(code), depth, results));
                },
                Some(&CompType::Unknown) | None => {},
            },
        }
    }
    Ok(())
}

/// Replay the structural-descent claim of the fixpoint `at` against the type
/// it is checked at.
///
/// # Specification
/// - requires: `body` is the fixpoint's body, scoped under its self binder, and
///   `expected` the type the fixpoint is checked at.
/// - ensures: success exactly when the type is a function out of a nominal data
///   application whose signature is in scope, or out of a path its words read
///   ([`CheckingContext::words`]), the body is a lambda whose body is a case on
///   that lambda's variable with one branch per constructor, each branch opens
///   exactly its constructor's fields by lambdas, and every occurrence of the
///   self variable in the motive and the branches is a call at a field of the
///   scrutinised constructor or at a function field's result.
/// - provides: the checker's half of the claim the kernel replays on its own; a
///   refusal here names the reason the kernel's walk would meet.
/// - fails: the first reason the walk meets, in the order above.
/// - panics: none.
///
/// # Errors
/// [`CheckRefusal::DescentNotReplayed`] with the reason.
///
/// # Adequacy
/// - hypothesis: L3 — every derived eliminator's fixpoint replays, including
///   one over a function field; a claim over a non-data type, a body that does
///   not case on its argument, a branch missing a field lambda, an unguarded
///   self reference and a call at the scrutinee itself each refuse by their own
///   reason, here and in the kernel.
/// - witness: `recursive_data::recursive_data::descent_claims_replay_or_are_refused_by_name`
/// - witness: `recursive_data::recursive_data::derived_eliminators_are_admitted_and_readmitted`
#[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(CheckRefusal::DescentNotReplayed { at: refused, .. }) if refused == at))]
pub fn replay(
    context: &mut CheckingContext<'_>,
    at: ComputationId,
    expected: CompTypeId,
    body: ComputationId,
) -> Result<(), CheckRefusal>
{
    let refuse = |reason| CheckRefusal::DescentNotReplayed { at, reason };
    let domain = match context.arena().comp_type(expected) {
        Some(&(CompType::Arrow { domain, .. } | CompType::Pi { domain, .. })) => domain,
        Some(
            &(CompType::Returner { .. }
            | CompType::With(..)
            | CompType::Element { .. }
            | CompType::Unknown),
        )
        | None => {
            return Err(refuse(DescentRefusal::NotOverData));
        },
    };
    // A path at a point free cells loop at descends over the words they mint.
    let declaration = match value_type_view(context.arena(), domain) {
        Ok(ValueTypeView::Data { declaration, .. }) => declaration,
        Ok(ValueTypeView::Path {
            carrier,
            left,
            right,
        }) => context
            .words(carrier, (left, right))
            .ok()
            .flatten()
            .ok_or_else(|| refuse(DescentRefusal::NotOverData))?,
        _ => return Err(refuse(DescentRefusal::NotOverData)),
    };
    let signature = context
        .consult_data(declaration)
        .ok_or_else(|| refuse(DescentRefusal::NotOverData))?;
    let arena = context.arena();
    let Some(&Computation::Lambda(inner)) = arena.computation(body)
    else {
        return Err(refuse(DescentRefusal::NotCaseOnArgument));
    };
    let Some(&Computation::DataCase {
        scrutinee,
        motive,
        ref branches,
    }) = arena.computation(inner)
    else {
        return Err(refuse(DescentRefusal::NotCaseOnArgument));
    };
    let on_argument = matches!(
        variable_level(arena, scrutinee, Binders::from(FIRST_FIELD)),
        Maybe::Present(level) if u32::from(level) == ARGUMENT_LEVEL
    );
    if !on_argument || branches.len() != signature.constructors().len() {
        return Err(refuse(DescentRefusal::NotCaseOnArgument));
    }
    let mut fixed = Branch {
        fields_end: Binders::from(FIRST_FIELD),
        links: Vec::new(),
    };
    walk(
        arena,
        &mut fixed,
        AnyNode::CompType(motive),
        Binders::from(FIRST_FIELD).deeper(),
    )
    .map_err(refuse)?;
    for (&case, fields) in branches.iter().zip(signature.constructors()) {
        let mut focus = case;
        let mut depth = Binders::from(FIRST_FIELD);
        for _field in fields {
            let Some(&Computation::Lambda(opened)) = arena.computation(focus)
            else {
                return Err(refuse(DescentRefusal::BranchNotOverFields));
            };
            focus = opened;
            depth = depth.deeper();
        }
        let mut branch = Branch {
            fields_end: depth,
            links: Vec::new(),
        };
        walk(arena, &mut branch, AnyNode::Computation(focus), depth).map_err(refuse)?;
    }
    Ok(())
}
