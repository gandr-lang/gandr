//! A theory's laws read through a handler's clauses.
//!
//! A handler over a theory is a model of it when every law of the theory
//! holds of its clauses: the law's two sides, each read through the clauses,
//! are one computation. [`read_law`] reads a law's sides over its
//! metavariables, each a variable bound outside the handler's context, the
//! first one named the innermost: a value metavariable stands as itself, and
//! one at the carrier, `k` or `k(t, …)`, as an unknown suspended computation
//! forced and applied to its arguments. [`obligation`] reads an operation
//! `op(v, …, bind x . t)` as its clause applied to the payload its values
//! make, each resumption of the clause's stack running `t` at what it is fed
//! ([`crate::rewrite::resume_through`]). The two sides then compare by
//! conversion, every metavariable rigid. The same laws, oriented, rewrite
//! the subject a scope over the theory handles before it runs ([`subject`]).
//!
//! # Examples
//!
//! ```text
//! rule putGet : put(s, get(bind t . k(t))) <=> put(s, k(s));
//! ```
//!
//! Read through the clauses `oper get(k) => k(4)` and `oper put(s, k) =>
//! k(unit)`, the left side runs `k` at `4` and the right side runs it at
//! `s`: the clauses tell the sides apart, so the handler is no model of the
//! law.
//!
//! # References
//!
//! - Filip Sieczkowski, Mateusz Pyzik and Dariusz Biernacki. "A General
//!   Fine-Grained Reduction Theory for Effect Handlers." _ICFP_ (2023), § 3:
//!   the contraction `handle.do` an operation's reading takes.
//! - Ezra Cooper. "The Marriage of Effects and Rewrites." arXiv:2302.02462
//!   (2023), § 2.1: the laws of global state.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::RuleIndex;
use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::TermNode;
use gandr_theory_levitation::TermView;

use crate::arena::ComputationId;
use crate::arena::CoreArena;
use crate::arena::ValueId;
use crate::effect::OperationName;
use crate::rewrite::Binders;
use crate::rewrite::resume_through;
use crate::rewrite::shift_computation_under;
use crate::syntax::ComponentCount;
use crate::syntax::Zone;

pub mod subject;

#[cfg(test)]
mod tests;

/// How many values an operation sends and is replied.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Arity
{
    /// The values its inputs before its continuation make.
    pub payload: ComponentCount,
    /// The values its continuation binds.
    pub reply: ComponentCount,
}

/// One node of a law's side read for a handler, in preorder.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum LawNode
{
    /// A value: a metavariable or a variable a continuation binds, at its
    /// index.
    Variable(DeBruijnIndex),
    /// A metavariable at the carrier, at its index: forced, then applied to
    /// each of the next `arguments` values.
    Carrier
    {
        /// Its index.
        index: DeBruijnIndex,
        /// How many values it is applied to.
        arguments: ComponentCount,
    },
    /// An operation, read through its clause: its payload's values next,
    /// then its continuation, beneath the payload's binder, the value the
    /// clause's stack is fed and, for a reply of several values, one binder
    /// per value.
    Operation
    {
        /// The operation.
        operation: OperationName,
        /// What it sends and is replied.
        arity: Arity,
        /// The binders between the metavariables and the operation.
        depth: Binders,
    },
}

/// A law of a theory read for a handler: its two sides over its
/// metavariables.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct ReadLaw
{
    /// The metavariables the sides stand beneath.
    pub metavariables: Binders,
    /// The side the law rewrites from, in preorder.
    pub left: Vec<LawNode>,
    /// The side it rewrites to, in preorder.
    pub right: Vec<LawNode>,
}

/// Why a law cannot be read through a handler's clauses.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum LawFault
{
    /// An operation the interface does not declare.
    Undeclared,
    /// An operation applied to other than its payload and one continuation,
    /// or a continuation binding other than its reply.
    Arity,
    /// A term no handler reads: a constructor, an atom, a results tuple, or a
    /// variable outside the position its sort takes.
    Unread,
}

/// A law the clauses of a scope owe, read through them: the two sides they
/// must identify.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct HandlerLaw
{
    /// The scope whose clauses the law is read through.
    pub scope: ComputationId,
    /// The law's place among its theory's rules.
    pub rule: RuleIndex,
    /// Its left side, read through the clauses, beneath its metavariables in
    /// the scope's context.
    pub left: ComputationId,
    /// Its right side, beneath the same metavariables.
    pub right: ComputationId,
}

/// Read a law's two sides for a handler whose operations `arity` gives.
///
/// # Specification
/// - requires: nothing.
/// - ensures: both sides in preorder over the law's metavariables, the first
///   one named the innermost; each metavariable and each variable a
///   continuation binds at its index where it is named; each operation at the
///   binders between the metavariables and it.
/// - fails: [`LawFault::Undeclared`] for an operation `arity` does not give;
///   [`LawFault::Arity`] for one applied to other than its payload and one
///   continuation binding its reply; [`LawFault::Unread`] for a constructor, an
///   atom, a results tuple, a binder outside a continuation, or a variable
///   outside the position its sort takes.
/// - panics: none.
///
/// # Errors
/// The first term the reading cannot take, left side first.
///
/// # Adequacy
/// - hypothesis: L3 — put-get read over its two metavariables, and a law
///   refused at each fault.
/// - witness: `handler::tests::put_get_reads_over_its_metavariables_2272`
/// - witness: `handler::tests::a_law_no_handler_reads_is_refused_by_its_fault_2272`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |read| !read.left.is_empty() && !read.right.is_empty()))]
#[inline]
pub fn read_law<Arities>(
    (left, right): (&FreeTerm, &FreeTerm),
    arity: Arities,
) -> Result<ReadLaw, LawFault>
where
    Arities: Fn(&Name) -> Option<Arity>,
{
    let mut reading = Reading {
        arity,
        metavariables: BTreeMap::new(),
        bound: Vec::new(),
    };
    let mut read_left = Vec::new();
    reading.computation(left.to_node(), Binders::NONE, &mut read_left)?;
    let mut read_right = Vec::new();
    reading.computation(right.to_node(), Binders::NONE, &mut read_right)?;
    Ok(ReadLaw {
        metavariables: Binders::from(
            u32::try_from(reading.metavariables.len()).unwrap_or(u32::MAX),
        ),
        left: read_left,
        right: read_right,
    })
}

/// A side of `law` read through `clauses`: each operation its clause's body
/// applied to its payload, the clause's stack resumed through the
/// operation's continuation.
///
/// # Specification
/// - requires: `side` is one of `law`'s sides; each clause body is a
///   computation of `arena` beneath its payload's binder then its stack's, in
///   the context the sides are read in.
/// - ensures: the side as a computation beneath `law`'s metavariables in that
///   context: a value its variable, a carrier metavariable forced and applied
///   to its arguments, an operation `(λp. B) v` where `v` is its payload's
///   values — none the unit, one itself, several their tuple — and `B` its
///   clause's body raised past the binders above the operation, each resumption
///   of its stack the operation's continuation run at what it is fed
///   ([`resume_through`]), split into its reply's values when it has several;
///   nothing when a clause is missing or the side is not one [`read_law`]
///   reads.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — get-get read through a constant clause, each operation
///   resumed through its continuation.
/// - witness: `handler::tests::a_side_resumes_each_clause_through_its_continuation_2272`
#[spec(ensures: |ret| ret.is_none_or(|side| arena.computation(side).is_some()))]
#[inline]
pub fn obligation(
    arena: &mut CoreArena,
    (law, side): (&ReadLaw, &[LawNode]),
    clauses: &BTreeMap<OperationName, ComputationId>,
) -> Option<ComputationId>
{
    let mut built: Vec<Built> = Vec::with_capacity(side.len());
    for node in side.iter().rev() {
        let next = match *node {
            LawNode::Variable(index) => {
                Built::Value(arena.value_variable(Zone::Intuitionistic, index))
            },
            LawNode::Carrier { index, arguments } => {
                let carrier = arena.value_variable(Zone::Intuitionistic, index);
                let mut applied = arena.computation_force(carrier);
                for _ in 0 .. usize::from(arguments) {
                    let Some(Built::Value(argument)) = built.pop()
                    else {
                        return None;
                    };
                    applied = arena.computation_application(applied, argument);
                }
                Built::Computation(applied)
            },
            LawNode::Operation {
                ref operation,
                arity,
                depth,
            } => {
                let payload = payload(arena, &mut built, arity.payload)?;
                let Some(Built::Computation(mut continuation)) = built.pop()
                else {
                    return None;
                };
                if usize::from(arity.reply) > 1 {
                    let fed =
                        arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
                    continuation = arena.computation_split(fed, arity.reply, continuation);
                }
                let &body = clauses.get(operation)?;
                let body = shift_computation_under(
                    arena,
                    body,
                    Binders::from(2_u32),
                    law.metavariables.beyond(depth),
                )
                .settle(arena);
                let resumed = resume_through(arena, body, continuation);
                let clause = arena.computation_lambda(resumed);
                Built::Computation(arena.computation_application(clause, payload))
            },
        };
        built.push(next);
    }
    match built.pop() {
        Some(Built::Computation(read)) if built.is_empty() => Some(read),
        Some(Built::Computation(_) | Built::Value(_)) | None => None,
    }
}

/// The payload an operation sends: the next `count` values `built` holds,
/// none the unit, one itself, several their tuple.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the payload the next `count` values make, each popped in order;
///   nothing when fewer than `count` values are next.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`obligation`].
/// - witness: `handler::tests::a_side_resumes_each_clause_through_its_continuation_2272`
#[spec(ensures: |ret| ret.is_none_or(|value| arena.value(value).is_some()))]
fn payload(
    arena: &mut CoreArena,
    built: &mut Vec<Built>,
    count: ComponentCount,
) -> Option<ValueId>
{
    let mut values = Vec::with_capacity(usize::from(count));
    for _ in 0 .. usize::from(count) {
        let Some(Built::Value(value)) = built.pop()
        else {
            return None;
        };
        values.push(value);
    }
    Some(match *values.as_slice() {
        [] => arena.value_unit(),
        [value] => value,
        [_, _, ..] => arena.value_tuple(&values),
    })
}

/// A node of a side as [`obligation`] builds it.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Built
{
    /// A value.
    Value(ValueId),
    /// A computation.
    Computation(ComputationId),
}

/// A law's reading in progress: the arity of each operation, each
/// metavariable named so far by the order it was first named in, and each
/// variable a continuation binds around the term being read, by the binder
/// it sits at.
///
/// # Specification
/// trivial.
struct Reading<Arities>
{
    /// The arity of each operation the interface declares.
    arity: Arities,
    /// Each metavariable by the order it was first named in.
    metavariables: BTreeMap<Name, u32>,
    /// Each variable a continuation binds, by the binder it sits at, the
    /// innermost last.
    bound: Vec<(Name, Binders)>,
}

impl<Arities> Reading<Arities>
where
    Arities: Fn(&Name) -> Option<Arity>,
{
    /// Read `term`, at `depth` binders beneath the metavariables, in
    /// computation position.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `out` gains `term`'s nodes in preorder: each operation down
    ///   its chain of continuations with its payload's values, then the
    ///   metavariable or instantiation of one as a carrier that ends the chain;
    ///   the variables continuations bind are released, as on entry.
    /// - fails: as [`read_law`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`read_law`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`read_law`].
    /// - witness: `handler::tests::put_get_reads_over_its_metavariables_2272`
    #[spec(captures: [before = out.len(), binding = self.bound.len()],
        ensures: |ret| (ret.is_err() || out.len() > before) && self.bound.len() == binding)]
    fn computation(
        &mut self,
        term: TermNode<'_>,
        depth: Binders,
        out: &mut Vec<LawNode>,
    ) -> Result<(), LawFault>
    {
        let binding = self.bound.len();
        let read = self.chain(term, depth, out);
        self.bound.truncate(binding);
        read
    }

    /// Read `term` as [`Self::computation`] does, leaving bound each
    /// variable a continuation down its chain binds.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`Self::computation`], but for the release of the
    ///   variables the continuations bind.
    /// - fails: as [`read_law`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`read_law`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`read_law`].
    /// - witness: `handler::tests::put_get_reads_over_its_metavariables_2272`
    #[spec(captures: before = out.len(), ensures: |ret| ret.is_err() || out.len() > before)]
    fn chain(
        &mut self,
        term: TermNode<'_>,
        depth: Binders,
        out: &mut Vec<LawNode>,
    ) -> Result<(), LawFault>
    {
        let (mut term, mut depth) = (term, depth);
        let mut inputs: Vec<TermNode<'_>> = Vec::new();
        loop {
            match term.view() {
                TermView::Var(name) => {
                    let index = self.metavariable(name, depth);
                    out.push(LawNode::Carrier {
                        index,
                        arguments: ComponentCount::from(0_usize),
                    });
                    return Ok(());
                },
                TermView::Inst { name, args } => {
                    let index = self.metavariable(name, depth);
                    let arguments: Vec<TermNode<'_>> = args.collect();
                    out.push(LawNode::Carrier {
                        index,
                        arguments: ComponentCount::from(arguments.len()),
                    });
                    for argument in arguments {
                        self.value(argument, depth, out)?;
                    }
                    return Ok(());
                },
                TermView::Op { name, args } => {
                    inputs.clear();
                    inputs.extend(args);
                    (term, depth) = self.operation(name, &inputs, depth, out)?;
                },
                TermView::Ctor { .. }
                | TermView::Results { .. }
                | TermView::Abs { .. }
                | TermView::Atom(_)
                | TermView::Lam { .. }
                | TermView::Bound(_) => return Err(LawFault::Unread),
            }
        }
    }

    /// Read the operation `name` applied to `inputs`, at `depth` binders
    /// beneath the metavariables, as far as its continuation's body.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `out` gains the operation at `depth` and its payload's
    ///   values; each variable its continuation binds is bound at its binder —
    ///   beneath the payload's binder, the fed value's and, for a reply of
    ///   several values, one binder per value — and the continuation's body is
    ///   returned with the binders it is read beneath.
    /// - fails: as [`read_law`] for one operation.
    /// - panics: none.
    ///
    /// # Errors
    /// As [`read_law`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`read_law`].
    /// - witness: `handler::tests::a_law_no_handler_reads_is_refused_by_its_fault_2272`
    #[spec(captures: before = out.len(), ensures: |ret| ret.is_err() || out.len() > before)]
    fn operation<'term>(
        &mut self,
        name: &Name,
        inputs: &[TermNode<'term>],
        depth: Binders,
        out: &mut Vec<LawNode>,
    ) -> Result<(TermNode<'term>, Binders), LawFault>
    {
        let arity = (self.arity)(name).ok_or(LawFault::Undeclared)?;
        let Some((&continuation, payload)) = inputs.split_last()
        else {
            return Err(LawFault::Arity);
        };
        if payload.len() != usize::from(arity.payload) {
            return Err(LawFault::Arity);
        }
        out.push(LawNode::Operation {
            operation: OperationName::from(name.as_ref()),
            arity,
            depth,
        });
        for &value in payload {
            self.value(value, depth, out)?;
        }
        // Beneath the payload's binder, then the value the stack is fed.
        let fed = depth.deeper();
        let mut body = continuation;
        let mut inner = fed.deeper();
        let replies = usize::from(arity.reply);
        for place in 0 .. replies {
            let TermView::Lam { var, mut args } = body.view()
            else {
                return Err(LawFault::Arity);
            };
            let Some(next) = args.next()
            else {
                return Err(LawFault::Arity);
            };
            // One reply value is the fed value; several are split from it,
            // each at its own binder past the fed value's.
            let at = if replies == 1 {
                fed
            }
            else {
                inner = inner.deeper();
                fed.deeper()
                    .beyond(Binders::from(u32::try_from(place).unwrap_or(u32::MAX)))
            };
            self.bound.push((var.clone(), at));
            body = next;
        }
        Ok((body, inner))
    }

    /// Read `term`, at `depth` binders beneath the metavariables, in value
    /// position.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `out` gains the variable `term` names: a metavariable or a
    ///   variable a continuation around it binds, at its index.
    /// - fails: [`LawFault::Unread`] for any other term.
    /// - panics: none.
    ///
    /// # Errors
    /// The term no value reads.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`read_law`].
    /// - witness: `handler::tests::a_law_no_handler_reads_is_refused_by_its_fault_2272`
    #[spec(captures: before = out.len(), ensures: |ret| ret.is_err() || out.len() == before.saturating_add(1))]
    fn value(
        &mut self,
        term: TermNode<'_>,
        depth: Binders,
        out: &mut Vec<LawNode>,
    ) -> Result<(), LawFault>
    {
        let index = match term.view() {
            TermView::Var(name) => self.metavariable(name, depth),
            TermView::Bound(name) => {
                let Some(&(_, at)) = self
                    .bound
                    .iter()
                    .rev()
                    .find(|&&(ref bound, _)| bound == name)
                else {
                    return Err(LawFault::Unread);
                };
                // reason: a binder around the term sits above it, so the
                // difference is positive.
                DeBruijnIndex::from(
                    u32::from(depth)
                        .saturating_sub(u32::from(at))
                        .saturating_sub(1),
                )
            },
            TermView::Ctor { .. }
            | TermView::Op { .. }
            | TermView::Results { .. }
            | TermView::Inst { .. }
            | TermView::Abs { .. }
            | TermView::Atom(_)
            | TermView::Lam { .. } => return Err(LawFault::Unread),
        };
        out.push(LawNode::Variable(index));
        Ok(())
    }

    /// The index of the metavariable `name` at `depth` binders beneath the
    /// metavariables, numbering it when it is named for the first time.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `depth` plus the order `name` was first named in, the first
    ///   one named the innermost.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`read_law`].
    /// - witness: `handler::tests::put_get_reads_over_its_metavariables_2272`
    #[spec(ensures: |ret| u32::from(ret) >= u32::from(depth))]
    fn metavariable(
        &mut self,
        name: &Name,
        depth: Binders,
    ) -> DeBruijnIndex
    {
        let next = u32::try_from(self.metavariables.len()).unwrap_or(u32::MAX);
        let &mut order = self.metavariables.entry(name.clone()).or_insert(next);
        DeBruijnIndex::from(u32::from(depth).saturating_add(order))
    }
}
