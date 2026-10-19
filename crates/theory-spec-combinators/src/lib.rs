//! Clause combinators: the bounded checks a `#[spec]` clause makes of state its
//! function has accumulated.
//!
//! An enforcing build evaluates every clause on every call. A clause that walks
//! a collection reached through `self` or a `&mut` parameter costs as much as
//! everything the collection has accumulated, so a constant-time push checked
//! that way makes a linear run quadratic. The workspace's rule is that **a
//! specification check costs no more than the function it checks**: a clause
//! walks the function's inputs and its output, a structural invariant is
//! checked once where the state is built, and accumulated state is read only
//! through a combinator that reads what changed since a point the clause
//! captured.
//!
//! Each function here is such a combinator. Its rustdoc carries a
//! `# Clause cost` section whose `- bound:` states what it reads; quenchant's
//! `spec_clause_traversal` lint stops following a clause's calls there.
//!
//! | Combinator | Claim | Reads |
//! | ---------- | ----- | ----- |
//! | [`Mark::of`] | the point a clause captures before a change | the length |
//! | [`appended`] | what a sequence gained since a mark | nothing; returns the suffix |
//! | [`pushed`] | a sequence grew by exactly one element, and it is this one | the length and the last element |
//! | [`sorted_around`] | a strictly increasing sequence stays so around an insertion point | the element and its two neighbours |
//!
//! Each answer that is a decision is a [`Holds`], read in a clause through
//! `bool::from`.
//!
//! # Decisions
//!
//! **Home.** The combinators live in a gandr crate in the first layer,
//! `theory`, so a crate of any layer may call them. A `workflow` crate was the
//! alternative closest to the gate it serves, but the layering forbids every
//! other layer from depending on one; quenchant, the specification tooling's
//! home, has no second consumer yet. The crate moves to quenchant once a second
//! consumer needs it.
//!
//! **Bounded reads only.** A combinator's bound depends on what changed since
//! the mark, never on what accumulated before it. A linear walk (membership in
//! a vector, equality of two collections, a set difference over whole sets) is
//! not a combinator: wrapping it would hide from the lint the walk the lint
//! exists to show. A clause whose check is linear in accumulated state carries
//! `#[expect(spec_clause_traversal, reason = "...")]` at its own site instead,
//! where the reviewer weighs the reason. The reason opens with its class:
//! `parity:` names the walk the function's body already makes, `bounded:`
//! states why the walk stays small, and `test fixture:` marks a clause of
//! test-only code. A domain claim that needs knowledge of one crate's types
//! (the caches of a parser's stack, the reach of an overlay) is a combinator in
//! that crate's private `spec` module, under the same rule. A type's own
//! invariant (`#[spec(maintains: …)]` on a struct or enum) expands into an
//! `impl` the macro generates, which an expectation on the type does not
//! reach: an invariant that walks the type calls a method of the type whose
//! `# Clause cost` bound carries the reason an expectation would, and a test
//! fixture's invariants take the expectation on their module. The reversal is
//! a measured case where a clause cannot state its claim within the function's
//! cost through a bounded read; that case is a new combinator here, never an
//! inlined walk.
//!
//! **Captured marks.** A [`Mark`] is a position: the length of a sequence
//! captured before a change, or the index a change wrote at. Clauses capture
//! it with `captures: before = Mark::of(&self.items)`. A sequence that is only
//! appended to between the capture and the check keeps every element before
//! the mark, so [`appended`] holds exactly what the function added.

// Module documentation that predates the shape lint: 1 heading outside the
// vocabulary and 1 budget exceeded. Each allow leaves with the rewrite that
// clears its count.
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    allow(
        module_doc_heading,
        module_doc_budget,
        reason = "module documentation that predates the shape lint"
    )
)]
#![no_std]

#[cfg(test)]
extern crate alloc;

pub mod holds;
pub mod sequence;

pub use crate::holds::Holds;
pub use crate::sequence::Mark;
pub use crate::sequence::appended;
pub use crate::sequence::pushed;
pub use crate::sequence::sorted_around;
