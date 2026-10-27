//! A theory's laws as rewrites of the subject a scope over the theory
//! handles.
//!
//! A scope `handle c : T { M } with { … }` runs `M` against a model of `T`, so
//! every law of `T` holds of what `M` requests: a run of requests that is an
//! instance of a law's oriented left side computes what its right side does.
//! [`subject_rule`] reads a law, in the direction the theory's order orients
//! it, as such a rewrite of `M`'s bind spine, and [`normalize`] rewrites the
//! spine by the rules until none applies, before the scope runs.
//!
//! A rule rewrites in place. Its right side makes some of its left side's
//! requests, in order and with the same payloads; each request it keeps
//! stays, and each it drops is replaced by returning, at its reply type, the
//! value its reply stands for on the right: the reply its carrier's
//! instantiation gives that binder, or the unit for a request replied
//! nothing. A value returned again is copied, so a rule copies only a
//! variable, a literal or the unit, and never runs a computation twice. A
//! dropped request's payload is checked at its payload type and bound before
//! the value is returned, so the subject the judgement reads still checks
//! every value it wrote, and runs each once. Every binder of the spine stays
//! where it was, so the rest of the subject is the rule's carrier untouched,
//! and the returns the rewrite leaves are transparent to the next match: a
//! bind of a returned value is the β-redex of the value it binds, which
//! commutes past a request.
//!
//! # Examples
//!
//! ```text
//! rule getGet : get(bind s . get(bind t . k(s, t))) <=> get(bind s . k(s, s));
//!
//! run a <- st.get(); run b <- st.get(); pure a + b
//! ```
//!
//! The second `get` is dropped and `b` is bound to `a`: `run a <- st.get(); b
//! ← return a; pure a + b`, one request where the subject wrote two.
//!
//! # References
//!
//! - Ezra Cooper. "The Marriage of Effects and Rewrites." arXiv:2302.02462
//!   (2023), § 2.1: the laws of global state, each oriented into a rewrite of
//!   the programs over the operations.
//! - `vault:01a16b8f-6aec-7282-b400-974aedeaa341` — lineage: an effect is a
//!   theory whose rules are its equations, and a program over it normalises by
//!   them before it runs, which [`normalize`] does to a scope's subject.
//! - `vault:01a178aa-a07b-7a23-bbcd-cf3893ccc160` — background: get-get,
//!   put-get and put-put are the laws that are rules, the ones [`subject_rule`]
//!   reads; a law under a grade condition is not one.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::RuleIndex;
use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::TermNode;
use gandr_theory_levitation::TermView;

use super::Arity;
use crate::arena::ComputationId;
use crate::arena::CoreArena;
use crate::arena::ValueId;
use crate::effect::OperationName;
use crate::rewrite::Binders;
use crate::rewrite::Carried;
use crate::rewrite::shift_value;
use crate::rewrite::shift_value_type;
use crate::syntax::ComponentCount;
use crate::syntax::Computation;
use crate::syntax::SplitMotive;
use crate::syntax::Value;
use crate::syntax::Zone;

#[cfg(test)]
mod tests;

/// The place of a request among those one side of a law makes.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Place(usize);

/// The place of a step on a subject's bind spine, outermost first.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct StepAt(usize);

/// Which side of a law is read: the left, which names each metavariable
/// first, or the right.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Reading
{
    /// The left side.
    Left,
    /// The right side.
    Right,
}

/// Whether a step is transparent to a match.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Transparent(bool);

/// Whether a value copies without running or duplicating a computation.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Atomic(bool);

/// A value a side of a law writes at a request's payload or at its carrier's
/// argument.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Written
{
    /// A metavariable, by the order the left side first names it in.
    Meta(usize),
    /// The reply of the request at this place on the same side.
    Reply(usize),
}

/// One request a side of a law makes.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct Request
{
    /// The operation requested.
    operation: OperationName,
    /// The values its payload is made of, in order.
    payload: Vec<Written>,
    /// Whether its continuation binds the value it is replied.
    replied: bool,
}

/// What a rule leaves where its left side makes a request.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Answer
{
    /// The request stays.
    Kept,
    /// The unit is returned in its place.
    Unit,
    /// The value the metavariable matched is returned in its place.
    Meta(usize),
    /// The reply of the kept request at this place on the left side is
    /// returned in its place.
    Reply(usize),
}

/// A law of a theory oriented as a rewrite of the subject a scope over the
/// theory handles.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct SubjectRule
{
    /// The law's place among its theory's rules.
    rule: RuleIndex,
    /// The requests the left side makes, in order.
    requests: Vec<Request>,
    /// What stands at each of them once the rule has rewritten it.
    answers: Vec<Answer>,
    /// How many metavariables the left side names at its payloads.
    metas: usize,
    /// The metavariables a dropped request is answered, whose values a
    /// rewrite copies.
    copied: BTreeSet<usize>,
}

impl SubjectRule
{
    /// The law's place among its theory's rules.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn rule(&self) -> RuleIndex
    {
        self.rule
    }
}

/// A side of a law read as the requests it makes and the carrier it ends in.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Side
{
    /// The requests, in order.
    requests: Vec<Request>,
    /// The carrier's metavariable.
    carrier: Name,
    /// The values the carrier is instantiated at, in order.
    arguments: Vec<Written>,
}

/// The law at `rule` rewriting `from` to `to`, for a scope whose operations
/// `arity` gives, as a rewrite of the scope's subject.
///
/// # Specification
/// - requires: `from` is the side the theory's order puts above `to`.
/// - ensures: the rule when both sides are a chain of requests, each operation
///   one `arity` gives applied to its payload's values and one continuation,
///   binding its reply when it is replied one value, ending in one carrier
///   metavariable; the left side's payload values are metavariables, each named
///   once, or replies of its earlier requests, and its carrier is instantiated
///   at distinct replies, every reply it binds among them; the right side makes
///   fewer requests, each the next of the left side's of its operation whose
///   payload is the same values, and instantiates the same carrier at values
///   each a reply the right side binds, standing where the left side's request
///   binding it stands, or a metavariable the left side names. A dropped
///   request is answered the unit when it is replied nothing, and otherwise the
///   value the right side instantiates its reply at: a metavariable named no
///   later than it, or the reply of a kept request before it. [`None`] for
///   every other law, which rewrites no subject.
/// - fails: never; a law no subject rewrite reads is [`None`].
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — get-get, put-get and put-put read as rewrites; a law
///   growing, reordering its requests, dropping a reply its right side gives no
///   value, or naming a metavariable twice on its left reads as none.
/// - witness: `handler::subject::tests::state_s_laws_read_as_rewrites_of_a_subject_2272`
/// - witness: `handler::subject::tests::a_law_no_rewrite_reads_is_none_2272`
#[spec(ensures: |ret| ret.as_ref().is_none_or(|read| read.rule == rule
    && read.requests.len() == read.answers.len()
    && read.answers.iter().any(|&answer| answer != Answer::Kept)))]
#[inline]
pub fn subject_rule<Arities>(
    rule: RuleIndex,
    (from, to): (&FreeTerm, &FreeTerm),
    arity: Arities,
) -> Option<SubjectRule>
where
    Arities: Fn(&Name) -> Option<Arity>,
{
    let mut metas: Vec<(Name, Place)> = Vec::new();
    let left = side(from.to_node(), &arity, &mut metas, Reading::Left)?;
    let right = side(to.to_node(), &arity, &mut metas, Reading::Right)?;
    if left.carrier != right.carrier
        || right.requests.len() >= left.requests.len()
        || left.arguments.len() != right.arguments.len()
    {
        return None;
    }
    // The carrier is instantiated at distinct replies, every reply among them.
    let mut instantiated = vec![None; left.requests.len()];
    for (place, &argument) in left.arguments.iter().enumerate() {
        let Written::Reply(request) = argument
        else {
            return None;
        };
        let slot = instantiated.get_mut(request)?;
        if slot.is_some() {
            return None;
        }
        *slot = Some(place);
    }
    for (request, slot) in left.requests.iter().zip(&instantiated) {
        if request.replied != slot.is_some() {
            return None;
        }
    }
    // Each right request is the next left one of its operation and payload.
    let mut kept: Vec<usize> = Vec::with_capacity(right.requests.len());
    let mut next = 0_usize;
    for request in &right.requests {
        let payload: Option<Vec<Written>> = request
            .payload
            .iter()
            .map(|&value| match value {
                Written::Meta(meta) => Some(Written::Meta(meta)),
                Written::Reply(earlier) => kept.get(earlier).copied().map(Written::Reply),
            })
            .collect();
        let payload = payload?;
        let found = left
            .requests
            .iter()
            .enumerate()
            .skip(next)
            .find(|&(_, candidate)| {
                candidate.operation == request.operation && candidate.payload == payload
            })
            .map(|(place, _)| place)?;
        kept.push(found);
        next = found.saturating_add(1);
    }
    // Where each left request stays on the right, when it does.
    let mut staying: Vec<Option<usize>> = vec![None; left.requests.len()];
    for (at, &place) in kept.iter().enumerate() {
        *staying.get_mut(place)? = Some(at);
    }
    let mut answers = Vec::with_capacity(left.requests.len());
    for (place, request) in left.requests.iter().enumerate() {
        let answer = if staying.get(place).is_some_and(Option::is_some) {
            Answer::Kept
        }
        else if let Some(&Some(at)) = instantiated.get(place) {
            match *right.arguments.get(at)? {
                Written::Meta(meta)
                    if metas
                        .get(meta)
                        .is_some_and(|&(_, first)| first <= Place(place)) =>
                {
                    Answer::Meta(meta)
                },
                Written::Reply(stays) => match kept.get(stays) {
                    Some(&earlier) if earlier < place => Answer::Reply(earlier),
                    Some(_) | None => return None,
                },
                Written::Meta(_) => return None,
            }
        }
        else if request.replied {
            return None;
        }
        else {
            Answer::Unit
        };
        answers.push(answer);
    }
    // A kept request's reply is instantiated where the left side's is.
    for (place, &argument) in left.arguments.iter().enumerate() {
        let Written::Reply(request) = argument
        else {
            return None;
        };
        if let Some(&Some(stays)) = staying.get(request)
            && right.arguments.get(place) != Some(&Written::Reply(stays))
        {
            return None;
        }
    }
    let copied = answers
        .iter()
        .filter_map(|&answer| match answer {
            Answer::Meta(meta) => Some(meta),
            Answer::Kept | Answer::Unit | Answer::Reply(_) => None,
        })
        .collect();
    Some(SubjectRule {
        rule,
        requests: left.requests,
        answers,
        metas: metas.len(),
        copied,
    })
}

/// Read `term` as a side of a law: its chain of requests and the carrier it
/// ends in, each metavariable numbered in `metas` by the order the left side
/// first names it in, beside the request naming it.
///
/// # Specification
/// - requires: the left side is read before the right, both into `metas`.
/// - ensures: as [`subject_rule`] reads a side; on the left a metavariable
///   named at a payload a second time, or at the carrier, is [`None`], and on
///   the right one the left side does not name.
/// - fails: never; a side out of shape is [`None`].
/// - panics: none.
/// - intension: one pass down the chain, so a long side costs no call stack.
///
/// # Adequacy
/// - hypothesis: L3 — as [`subject_rule`].
/// - witness: `handler::subject::tests::state_s_laws_read_as_rewrites_of_a_subject_2272`
/// - witness: `handler::subject::tests::a_law_no_rewrite_reads_is_none_2272`
#[spec(ensures: |ret| ret.as_ref().is_none_or(|read| read.requests.iter().all(|request| request.payload.iter().all(|&value| match value {
    Written::Meta(meta) => meta < metas.len(),
    Written::Reply(_) => true,
}))))]
fn side<Arities>(
    term: TermNode<'_>,
    arity: &Arities,
    metas: &mut Vec<(Name, Place)>,
    reading: Reading,
) -> Option<Side>
where
    Arities: Fn(&Name) -> Option<Arity>,
{
    let mut requests: Vec<Request> = Vec::new();
    // Each variable a continuation binds, beside the request it replies.
    let mut bound: Vec<(&Name, Place)> = Vec::new();
    let mut term = term;
    loop {
        match term.view() {
            TermView::Op { name, args } => {
                let declared = arity(name)?;
                let mut inputs: Vec<TermNode<'_>> = args.collect();
                let continuation = inputs.pop()?;
                if inputs.len() != usize::from(declared.payload) {
                    return None;
                }
                let place = Place(requests.len());
                let mut payload = Vec::with_capacity(inputs.len());
                for input in inputs {
                    payload.push(match input.view() {
                        TermView::Var(meta) => {
                            named(metas, meta, (reading == Reading::Left).then_some(place))?
                        },
                        TermView::Bound(variable) => Written::Reply(replied(&bound, variable)?.0),
                        TermView::Ctor { .. }
                        | TermView::Op { .. }
                        | TermView::Results { .. }
                        | TermView::Inst { .. }
                        | TermView::Abs { .. }
                        | TermView::Atom(_)
                        | TermView::Lam { .. } => return None,
                    });
                }
                let replied = match usize::from(declared.reply) {
                    0 => {
                        term = continuation;
                        false
                    },
                    1 => {
                        let TermView::Lam { var, mut args } = continuation.view()
                        else {
                            return None;
                        };
                        bound.push((var, place));
                        term = args.next()?;
                        true
                    },
                    _ => return None,
                };
                requests.push(Request {
                    operation: OperationName::from(name.as_ref()),
                    payload,
                    replied,
                });
            },
            TermView::Var(carrier) => {
                return Some(Side {
                    requests,
                    carrier: carrier.clone(),
                    arguments: Vec::new(),
                });
            },
            TermView::Inst { name, args } => {
                let mut arguments = Vec::with_capacity(args.len());
                for argument in args {
                    arguments.push(match argument.view() {
                        TermView::Bound(variable) => Written::Reply(replied(&bound, variable)?.0),
                        TermView::Var(meta) if reading == Reading::Right => {
                            named(metas, meta, None)?
                        },
                        TermView::Var(_)
                        | TermView::Ctor { .. }
                        | TermView::Op { .. }
                        | TermView::Results { .. }
                        | TermView::Inst { .. }
                        | TermView::Abs { .. }
                        | TermView::Atom(_)
                        | TermView::Lam { .. } => return None,
                    });
                }
                return Some(Side {
                    requests,
                    carrier: name.clone(),
                    arguments,
                });
            },
            TermView::Ctor { .. }
            | TermView::Results { .. }
            | TermView::Abs { .. }
            | TermView::Atom(_)
            | TermView::Lam { .. }
            | TermView::Bound(_) => return None,
        }
    }
}

/// The metavariable `name`: numbered next beside `first`, the request naming
/// it, when the left side names it for the first time, or the number the left
/// side gave it.
///
/// # Specification
/// - ensures: on the left (`first` present) a fresh number, [`None`] when
///   `name` is numbered already; on the right its number, [`None`] when it is
///   not.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`subject_rule`].
/// - witness: `handler::subject::tests::a_law_no_rewrite_reads_is_none_2272`
#[spec(ensures: |ret| ret.is_none_or(|value| matches!(value, Written::Meta(meta) if meta < metas.len())))]
fn named(
    metas: &mut Vec<(Name, Place)>,
    name: &Name,
    first: Option<Place>,
) -> Option<Written>
{
    let known = metas.iter().position(|&(ref held, _)| held == name);
    match (known, first) {
        (Some(meta), None) => Some(Written::Meta(meta)),
        (None, Some(place)) => {
            metas.push((name.clone(), place));
            Some(Written::Meta(metas.len().saturating_sub(1)))
        },
        (Some(_), Some(_)) | (None, None) => None,
    }
}

/// The request whose continuation binds `variable`, innermost first.
///
/// # Specification
/// trivial.
fn replied(
    bound: &[(&Name, Place)],
    variable: &Name,
) -> Option<Place>
{
    bound
        .iter()
        .rev()
        .find(|&&(name, _)| name == variable)
        .map(|&(_, place)| place)
}

/// One step of a subject's bind spine.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Frame
{
    /// `x ← bound; …`, at its node.
    Bind
    {
        /// The bind.
        node: ComputationId,
        /// The computation it binds the value of.
        bound: ComputationId,
    },
    /// A split at the ambient motive, at its node.
    Split
    {
        /// The split.
        node: ComputationId,
        /// The value split.
        scrutinee: ValueId,
        /// How many components it binds.
        arity: ComponentCount,
    },
}

/// A subject's bind spine: each step with the binders above it, and the
/// computation it ends in.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Spine
{
    /// Each step, outermost first, beside the binders between the subject and
    /// it.
    frames: Vec<(Frame, u32)>,
    /// What the last step continues to.
    tail: ComputationId,
    /// The computation each rewritten bind binds now, by the step's place.
    answered: BTreeMap<usize, ComputationId>,
}

/// Where a rule's left side matched: the step of each of its requests, and
/// each metavariable's value beside the binders it stands beneath.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Matched
{
    /// The step of each request, in order.
    steps: Vec<usize>,
    /// Each metavariable's value and its depth.
    metas: Vec<Option<(ValueId, u32)>>,
}

/// `subject`, the subject of a scope whose capability is its outermost
/// binder, rewritten by `rules` until none applies.
///
/// # Specification
/// - requires: `subject` is a computation of `arena` beneath the scope's
///   capability, its innermost binder; each rule is one [`subject_rule`] read
///   for the scope's operations.
/// - ensures: the subject read along its bind spine — binds' rests and the
///   bodies of splits at the ambient motive — with each run of requests of the
///   capability that instantiates a rule's left side rewritten by it, the first
///   rule in order at the outermost run first, again from the top until no rule
///   matches: a match reads the left side's requests at steps that are each a
///   bind of an exercise of the capability, the steps between two of them each
///   a bind of a returned value or a split of nothing; a payload's values are
///   the metavariables' values, each mentioning no binder of an earlier request
///   of the match and, where a dropped request is answered it, a variable, a
///   literal or the unit, and the earlier requests' replies the side names.
///   Each request the rule drops binds, in its exercise's place, the value its
///   answer gives ascribed its reply type, after binding its payload ascribed
///   its payload type when it sends one; every other node of the spine stays.
///   `carried` gains, for each step rebuilt, the step beside its rebuilding,
///   and for each exercise replaced, the exercise beside each computation
///   standing in its place. `subject` itself, `carried` unchanged, when no rule
///   matches.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// - reason: the `loop` rewriting the spine, not recursion.
/// - measure: the requests on the spine: each rewrite replaces at least one by
///   a returned value and adds none.
///
/// # Adequacy
/// - hypothesis: L3 — two gets normalise to one and three to one, a put then a
///   get to the put, two puts to the second, a get beside another capability's
///   request or behind a step that is no return stays, and a payload naming an
///   earlier request's reply refuses a rule whose metavariable stands there, as
///   a value a computation returns refuses a rule that would answer a dropped
///   request with it.
/// - witness: `handler::subject::tests::two_gets_normalise_to_one_2272`
/// - witness: `handler::subject::tests::state_s_laws_normalise_a_spine_2272`
/// - witness: `handler::subject::tests::a_run_no_rule_instantiates_stays_2272`
#[spec(captures: before = carried.len(), ensures: |ret| (ret == subject) == (carried.len() == before)
    && arena.computation(ret).is_some())]
#[inline]
pub fn normalize(
    arena: &mut CoreArena,
    subject: ComputationId,
    rules: &[SubjectRule],
    carried: &mut Vec<Carried>,
) -> ComputationId
{
    if rules.is_empty() {
        return subject;
    }
    let mut spine = spine(arena, subject);
    loop {
        let found = {
            let view: &CoreArena = arena;
            (0 .. spine.frames.len()).find_map(|step| {
                rules.iter().find_map(|rule| {
                    matched(view, &spine, StepAt(step), rule).map(|matched| (rule, matched))
                })
            })
        };
        let Some((rule, matched)) = found
        else {
            break;
        };
        let mut progressed = false;
        for ((&answer, request), &step) in
            rule.answers.iter().zip(&rule.requests).zip(&matched.steps)
        {
            let Some((answered, minted, exercise)) =
                answer_at(arena, &spine, (StepAt(step), answer, request), &matched)
            else {
                continue;
            };
            let _rewritten = spine.answered.insert(step, answered);
            carried.extend(
                minted
                    .into_iter()
                    .map(|standing| Carried::Computation(exercise, standing)),
            );
            progressed = true;
        }
        if !progressed {
            break;
        }
    }
    if spine.answered.is_empty() {
        return subject;
    }
    let mut current = spine.tail;
    let mut changed = false;
    for (step, &(frame, _)) in spine.frames.iter().enumerate().rev() {
        let answered = spine.answered.get(&step).copied();
        if answered.is_none() && !changed {
            current = match frame {
                Frame::Bind { node, .. } | Frame::Split { node, .. } => node,
            };
            continue;
        }
        let (node, rebuilt) = match frame {
            Frame::Bind { node, bound } => (
                node,
                arena.computation_bind(answered.unwrap_or(bound), current),
            ),
            Frame::Split {
                node,
                scrutinee,
                arity,
            } => (node, arena.computation_split(scrutinee, arity, current)),
        };
        carried.push(Carried::Computation(node, rebuilt));
        current = rebuilt;
        changed = true;
    }
    current
}

/// `subject`'s bind spine, read down binds' rests and the bodies of splits at
/// the ambient motive.
///
/// # Specification
/// - ensures: every step with the binders above it, a bind adding one and a
///   split its arity, and the first computation that is neither; no step
///   answered.
/// - panics: none.
///
/// # Termination
/// - reason: the `loop` down the spine, not recursion.
/// - measure: the nodes beneath the current one: the arena is acyclic.
///
/// # Adequacy
/// - hypothesis: L3 — as [`normalize`].
/// - witness: `handler::subject::tests::two_gets_normalise_to_one_2272`
#[spec(ensures: |ret| ret.answered.is_empty())]
fn spine(
    arena: &CoreArena,
    subject: ComputationId,
) -> Spine
{
    let mut frames = Vec::new();
    let (mut current, mut depth) = (subject, 0_u32);
    loop {
        match arena.computation(current) {
            Some(&Computation::Bind(bound, rest)) => {
                frames.push((
                    Frame::Bind {
                        node: current,
                        bound,
                    },
                    depth,
                ));
                depth = depth.saturating_add(1);
                current = rest;
            },
            Some(&Computation::Split {
                scrutinee,
                arity,
                motive: SplitMotive::Ambient,
                body,
            }) => {
                frames.push((
                    Frame::Split {
                        node: current,
                        scrutinee,
                        arity,
                    },
                    depth,
                ));
                depth = depth.saturating_add(u32::try_from(usize::from(arity)).unwrap_or(u32::MAX));
                current = body;
            },
            _ => {
                return Spine {
                    frames,
                    tail: current,
                    answered: BTreeMap::new(),
                };
            },
        }
    }
}

/// Where `rule`'s left side matches `spine` from `start`.
///
/// # Specification
/// - ensures: as [`normalize`] reads a match whose first request is the step at
///   `start`; [`None`] where none is.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`normalize`].
/// - witness: `handler::subject::tests::a_run_no_rule_instantiates_stays_2272`
#[spec(ensures: |ret| ret.as_ref().is_none_or(|found| found.steps.len() == rule.requests.len()
    && found.steps.first() == Some(&start.0)))]
fn matched(
    arena: &CoreArena,
    spine: &Spine,
    start: StepAt,
    rule: &SubjectRule,
) -> Option<Matched>
{
    let mut found = Matched {
        steps: Vec::with_capacity(rule.requests.len()),
        metas: vec![None; rule.metas],
    };
    let mut step = start.0;
    // The level of each earlier request's binder, counted from the subject's
    // root.
    let mut levels: BTreeSet<u32> = BTreeSet::new();
    for request in &rule.requests {
        if !found.steps.is_empty() {
            while transparent(arena, spine, StepAt(step)).0 {
                step = step.saturating_add(1);
            }
        }
        let &(Frame::Bind { bound, .. }, depth) = spine.frames.get(step)?
        else {
            return None;
        };
        if spine.answered.contains_key(&step) {
            return None;
        }
        let Some(&Computation::Exercise {
            capability,
            ref operation,
            payload,
            ..
        }) = arena.computation(bound)
        else {
            return None;
        };
        let at = |index: u32| Value::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(index),
        };
        if arena.value(capability) != Some(&at(depth)) || *operation != request.operation {
            return None;
        }
        let values: Vec<ValueId> = match (request.payload.len(), arena.value(payload)) {
            (0, _) => Vec::new(),
            (1, _) => Vec::from([payload]),
            (count, Some(&Value::Tuple(ref members))) if members.len() == count => members.to_vec(),
            _ => return None,
        };
        for (&written, &value) in request.payload.iter().zip(&values) {
            match written {
                Written::Meta(meta) => {
                    let mentions = arena.value_support(value).is_some_and(|support| {
                        support.indices(Zone::Intuitionistic).any(|index| {
                            let index = u32::from(index);
                            index < depth
                                && levels.contains(&depth.saturating_sub(index).saturating_sub(1))
                        })
                    });
                    // A value the rule returns again is copied: only a
                    // variable, a literal or the unit copies without running
                    // or duplicating a computation it holds.
                    let copied = rule.copied.contains(&meta);
                    if mentions || (copied && !atomic(arena, value).0) {
                        return None;
                    }
                    *found.metas.get_mut(meta)? = Some((value, depth));
                },
                Written::Reply(request) => {
                    let replying = *found.steps.get(request)?;
                    let &(_, above) = spine.frames.get(replying)?;
                    if arena.value(value)
                        != Some(&at(depth.saturating_sub(above).saturating_sub(1)))
                    {
                        return None;
                    }
                },
            }
        }
        found.steps.push(step);
        let _fresh = levels.insert(depth);
        step = step.saturating_add(1);
    }
    Some(found)
}

/// Whether the step at `step` is transparent to a match: a bind a rewrite
/// answered, a bind of a returned value, or a split of nothing.
///
/// # Specification
/// trivial.
fn transparent(
    arena: &CoreArena,
    spine: &Spine,
    step: StepAt,
) -> Transparent
{
    Transparent(match spine.frames.get(step.0) {
        Some(&(Frame::Bind { bound, .. }, _)) => {
            spine.answered.contains_key(&step.0)
                || matches!(arena.computation(bound), Some(&Computation::Return(_)))
        },
        Some(&(Frame::Split { arity, .. }, _)) => usize::from(arity) == 0,
        None => false,
    })
}

/// Whether `value` copies without running or duplicating a computation: a
/// variable, a literal or the unit.
///
/// # Specification
/// trivial.
fn atomic(
    arena: &CoreArena,
    value: ValueId,
) -> Atomic
{
    Atomic(match arena.value(value) {
        Some(&(Value::Variable { .. } | Value::Literal(_))) => true,
        Some(&Value::Tuple(ref members)) => members.is_empty(),
        _ => false,
    })
}

/// What a dropped request at `step` binds in its exercise's place: the value
/// `answer` gives returned at the request's reply type, after its payload
/// checked at its payload type when `request` sends one; beside every
/// computation minted for it and the exercise it replaces. [`None`] for a
/// kept request.
///
/// # Specification
/// - requires: `matched` is where the rule `request` belongs to matched.
/// - ensures: for a dropped request at depth `d` of an operation the exercise's
///   signature types `P ↠ R`, `(return w : F R)` with `w` the unit, the
///   metavariable's value raised past the binders between its request and this
///   one, or the variable naming the kept request's reply; `p ← (return v : F
///   P); (return w : F R)`, `w` and `R` past one binder more, when the request
///   sends a payload `v`, so the payload is checked where it was written and
///   runs once.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`normalize`].
/// - witness: `handler::subject::tests::state_s_laws_normalise_a_spine_2272`
#[spec(ensures: |ret| ret.as_ref().is_none_or(|&(answered, ref minted, _)| arena.computation(answered).is_some() && minted.contains(&answered)))]
fn answer_at(
    arena: &mut CoreArena,
    spine: &Spine,
    (step, answer, request): (StepAt, Answer, &Request),
    matched: &Matched,
) -> Option<(ComputationId, Vec<ComputationId>, ComputationId)>
{
    let &(Frame::Bind { bound, .. }, depth) = spine.frames.get(step.0)?
    else {
        return None;
    };
    let Some(&Computation::Exercise {
        payload,
        ref signature,
        ref operation,
        ..
    }) = arena.computation(bound)
    else {
        return None;
    };
    let (sent_at, replied_at) = signature
        .operations()
        .find(|declared| declared.name == *operation)
        .map(|declared| (declared.payload, declared.reply))?;
    let sends = !request.payload.is_empty();
    let past = Binders::from(u32::from(sends));
    let at = depth.saturating_add(u32::from(sends));
    let value = match answer {
        Answer::Kept => return None,
        Answer::Unit => arena.value_unit(),
        Answer::Meta(meta) => {
            let (value, from) = (*matched.metas.get(meta)?)?;
            shift_value(arena, value, Binders::from(at.saturating_sub(from))).settle(arena)
        },
        Answer::Reply(kept) => {
            let replying = *matched.steps.get(kept)?;
            let &(_, above) = spine.frames.get(replying)?;
            arena.value_variable(
                Zone::Intuitionistic,
                DeBruijnIndex::from(at.saturating_sub(above).saturating_sub(1)),
            )
        },
    };
    let replied_at = shift_value_type(arena, replied_at, past).settle(arena);
    let replied_at = arena.comp_type_returner(replied_at);
    let bare = arena.computation_return(value);
    let returned = arena.computation_ascribe(bare, replied_at);
    if !sends {
        return Some((returned, Vec::from([bare, returned]), bound));
    }
    let sent_at = arena.comp_type_returner(sent_at);
    let sent = arena.computation_return(payload);
    let checked = arena.computation_ascribe(sent, sent_at);
    let answered = arena.computation_bind(checked, returned);
    Some((
        answered,
        Vec::from([sent, checked, bare, returned, answered]),
        bound,
    ))
}
