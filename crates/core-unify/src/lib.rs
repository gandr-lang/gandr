//! The metacontext and the solver an elaborator calls for the metavariables
//! it creates: bindings forced most generally, the rest waiting in one store.
//!
//! A metavariable is a value hole a [`Metas`] declares, with the number of
//! binders its context holds; the core gains no former. [`solve()`] takes
//! equations between values, value types and computation types, each posed
//! under some binders, and binds a metavariable only where an equation forces
//! the binding: a metavariable against a value, or the decode of one against
//! a type, whose quote it then stands for. A solution naming no binder outside
//! the metavariable's context, by the support the core carries on every node,
//! is lowered into the context, minting nothing.
//!
//! An equation the run cannot answer most generally is never guessed at and
//! never stops the run: it waits in the metacontext's store
//! ([`Metas::postponed`]) with its [`Reason`] and the unsolved metavariables
//! that block it, and is posed again when one of them is bound. What still
//! waits when the caller's declaration ends is refused there by name. A
//! [`Refutation`] is evidence that no solution exists, taken only from what no
//! instantiation changes.
//!
//! # Examples
//!
//! ```
//! use gandr_core_term::Binders;
//! use gandr_core_term::CoreArena;
//! use gandr_core_term::Value;
//! use gandr_core_term::hole::HoleId;
//! use gandr_core_unify::Equation;
//! use gandr_core_unify::Metas;
//! use gandr_core_unify::Side;
//! use gandr_core_unify::Verdict;
//! use gandr_core_unify::solve;
//! use gandr_kernel_strata::Level;
//! use gandr_kernel_term::BaseType;
//! use quenchant_shape::shape::Maybe;
//!
//! // `same @[a : Type] (x : a) : a` called at an integer: the parameter's
//! // type is the decode of a metavariable, the argument's the integer type.
//! let mut arena = CoreArena::new();
//! let hole = HoleId::from(0_u32);
//! let mut metas = Metas::new();
//! let Maybe::Present(meta) = metas.declare(hole, Binders::NONE)
//! else {
//!     unreachable!()
//! };
//! let code = arena.value_hole(hole);
//! let parameter = arena.value_type_element(code, Level::zero());
//! let integer = arena.value_type_base(BaseType::Integer);
//! let equation = Equation::new(
//!     Binders::NONE,
//!     Side::ValueType(parameter),
//!     Side::ValueType(integer),
//! );
//! assert_eq!(Verdict::Solved, solve(&mut arena, &mut metas, &[equation]));
//! let Maybe::Present(solution) = metas.solution(meta)
//! else {
//!     unreachable!()
//! };
//! assert_eq!(Some(&Value::Quote(integer)), arena.value(solution));
//! ```
//!
//! # Boundaries
//!
//! - The metavariables are values, which every implicit argument is; no
//!   computation hole is one.
//! - A metavariable applied to arguments waits as [`Reason::Spine`]: inverting
//!   a spine of distinct variables is the next rung.
//! - A value mentioning a metavariable of a wider context waits as
//!   [`Reason::Pruning`]: narrowing that metavariable's context is the rung
//!   after.
//! - A definition is never unfolded: the pair waits as [`Reason::Unfolding`].
//! - Two decodes compare their codes, and a decode of a metavariable against a
//!   type binds it to the type's quote: both are most general while decoding is
//!   injective on codes.
//! - Nothing here checks a solution's type; the judgement that reads the solved
//!   term checks it.
//!
//! # References
//!
//! - Dale Miller. "A Logic Programming Language with Lambda-Abstraction,
//!   Function Variables, and Simple Unification." _Journal of Logic and
//!   Computation_ 1(4), 1991, 497–536. `doi:10.1093/logcom/1.4.497` — the
//!   pattern fragment whose forced solutions are most general.
//! - Andreas Abel and Brigitte Pientka. "Higher-Order Dynamic Pattern
//!   Unification for Dependent Types and Records." _TLCA 2011_, LNCS 6690,
//!   10–26. `doi:10.1007/978-3-642-21691-6_5` — contextual metavariables,
//!   pruning and the occurs check read through solutions.
//! - Conor `McBride`. "Everybody's Got To Be Somewhere." _MSFP 2018_, EPTCS
//!   275, 53–69. `doi:10.4204/EPTCS.275.6` — the support carried on every node
//!   that scopes a solution.
//! - Jesper Cockx and Dominique Devriese. "Proof-Relevant Unification:
//!   Dependent Pattern Matching with Only the Axioms of Your Type Theory."
//!   _Journal of Functional Programming_ 28, 2018.
//!   `doi:10.1017/S095679681800014X` — the conflict and cycle rules, the only
//!   refutations.
//! - Andrew Slattery and Jonathan Sterling. "Bidirectional Elaborators à la
//!   Carte." 2026. `arXiv:2607.09564` — postponement as partiality over one
//!   dominance, whose constraint actions commute.

#![no_std]

extern crate alloc;

mod meta;
mod solve;

pub use crate::meta::MetaCount;
pub use crate::meta::MetaId;
pub use crate::meta::Metas;
pub use crate::meta::declaration;
pub use crate::meta::meta_lookup;
pub use crate::solve::Equation;
pub use crate::solve::Postponed;
pub use crate::solve::Reason;
pub use crate::solve::Refutation;
pub use crate::solve::Side;
pub use crate::solve::Verdict;
pub use crate::solve::solve;
