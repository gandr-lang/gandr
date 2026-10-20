//! Finite shapes for gandr: decidable subshapes of finite carriers, the outer
//! pushout of two of them, and entailment between face formulas in the
//! conjunctive band and its column disjunctions, decided with a derivation or
//! a countermodel that a validator checks without the decision procedure.
//!
//! # The shape theory
//!
//! The crate states a shape parameter `ft` in the sense of [`FaceTT`]: the
//! shapes a context may bind, their subshapes, and the face formulas a
//! boundary is written in. Every shape is a finite carrier.
//!
//! | Part | Statement |
//! | ---- | --------- |
//! | Shapes | finite carriers `Fin(m)`, sized by [`PointCount`] |
//! | Subshapes | [`Subshape`]: a decidable subset with its complement, meet and union ([`SetOperation`]) and inclusion ([`Subshape::included`]) |
//! | Cofibrations | [`Cofibration`]: an inclusion presented with its complement in the target |
//! | Pushouts | [`UnionSquare`]: the outer pushout of two subshapes over their meet, with its universal map [`UnionSquare::mediator`] |
//! | Atoms | `x ∈ S` ([`Node::Member`]) for a [`Variable`] `x` of carrier `Fin(m)` and a subshape `S` of `Fin(m)` |
//! | Formers | `⊤`, `⊥`, `∧`, `∨` ([`Node`]) |
//! | Axioms | the bounded distributive lattice laws; membership read in the actual subset |
//!
//! The union square is outer data: its four blocks — both, left only, right
//! only, neither — partition the carrier, the union is the pushout of the two
//! inclusions of the meet, and two maps out of the legs that agree on the meet
//! glue to exactly one map out of the union. It is not a colimit in a
//! graphical site, and no type-valued pushout elimination is implemented here.
//!
//! # Decision: finite shapes and no interval
//!
//! - **Choice.** Shapes are finite carriers and nothing else: no interval, no
//!   endpoint atoms, no diagonal, no Glue. The consumers of the shape theory
//!   are extension types over first-order data — records, and metavariables
//!   whose boundary is constrained — and what they restrict along is a
//!   decidable subshape of a finite carrier.
//! - **Alternatives.** The cubical interval with its face lattice and Glue
//!   ([CCHM]), which buys a univalent universe by Kan composition at the cost
//!   of face decomposition inside the evaluator. An affine bridge interval as a
//!   shape sort, for internal parametricity: bridges in gandr are interval-free
//!   instead, the local theory of [ACKS] in observational form, defined by the
//!   same recursion over codes that defines identity. An affine sort also has
//!   no home in the framework itself: in a structural theory of signatures
//!   ([Kaposi–Xie], Definition 13) context comprehension and substitution give
//!   every representable sort its diagonal, whatever operations the signature
//!   declares, and `FaceTT`'s face theories carry variable equality besides.
//! - **Reversal.** A consumer that needs a diagonal, an interval or an endpoint
//!   face arrives with the fixture that needs it.
//!
//! # The decided band
//!
//! [`Problem::new`] admits a query over a context of finite carriers whose
//! premise is a conjunction of atoms (`⊤`, `⊥`, membership) and whose
//! conclusion is a conjunction of atoms and column disjunctions. A column
//! disjunction `x ∈ S₁ ∨ … ∨ x ∈ Sₙ` has every atom on one variable, and
//! holds exactly when `x ∈ S₁ ∪ … ∪ Sₙ`: the disjunction is finite over that
//! variable's carrier, never over an interval. A disjunction in a premise, or
//! one whose atoms name two variables, is refused by its node
//! ([`ShapeError::Disjunction`]). Entailment is at every assignment of a point
//! to each variable. [`decide`] answers the band in polynomial time:
//! intersect the premise's atoms variable by variable, then test each
//! conclusion conjunct — an atom's subshape or a column's union — for
//! inclusion.
//!
//! The column disjunction is the shape of a coverage question: a match's arms
//! over one column of a data type are one atom each over that type's
//! constructors, the arms cover the column when `⊤` entails their
//! disjunction, and a countermodel is a constructor no arm takes.
//!
//! The composite language — disjunctions across variables, or in a premise —
//! is not offered. Entailment there is coNP-complete ([Rose–Licata]), and
//! finite membership alone reaches the bar: over two-point carriers read
//! `x ∈ {1}` as a positive literal and `x ∈ {0}` as a negative one, and a
//! conjunctive normal form entails `⊥` exactly when it is unsatisfiable. The
//! extension type's questions at a boundary are atomic or conjunctive, and
//! gandr's transport is replay over a trace, which consults no entailment
//! procedure at all. `FaceTT`'s own algorithmic assumption is decidable
//! atomic entailment; a client meeting `φ ∨ ψ` across variables decomposes it
//! into one question per disjunct.
//!
//! # Evidence
//!
//! [`decide`] returns [`Evidence::Holds`] with a [`Derivation`] or
//! [`Evidence::Refuted`] with a [`Countermodel`]. A derivation is one of four
//! forms: a variable with an empty carrier (no assignment exists); a `⊥` the
//! premise reaches; premise atoms on one variable whose meet is empty; or, for
//! each conclusion conjunct, the premise atoms on its variable whose meet the
//! conjunct includes — `∧`-elimination, meet, monotonicity, `∨`-introduction
//! and `∧`-introduction in the lattice. A countermodel is a total assignment.
//!
//! Both are untrusted public data. [`Derivation::validate`] reads the cited
//! atoms out of the query, recomputes their meet and each column's union with
//! the subshape operations and checks the claimed emptiness or inclusion;
//! [`Countermodel::validate`] checks the assignment's length and bounds and
//! evaluates both formulas at it. Neither calls [`decide`], and the decision
//! shares no code with them: it intersects and unites raw membership tables.
//! The agreement suite checks every answer against a truth table computed by
//! a separately written evaluator.
//! This is executable evidence, not a machine-checked proof of the Rust.
//!
//! Evidence by case analysis over the carriers — split a variable into its
//! points, close each branch when the premise is false or the conclusion
//! true — is the alternative not taken. It decides the composite language
//! too, but a leaf must settle the whole conclusion, so its proofs of a
//! conjunctive conclusion grow with the product of the carriers:
//! `∧ᵢ xᵢ ∈ {0,1} ⊢ ∧ᵢ xᵢ ∈ {0,1}` over `n` three-point carriers takes
//! `3·2ⁿ − 2` rules, where a [`Derivation::Supported`] cites `n` atoms. It
//! returns only if a band needing case analysis is admitted.
//!
//! # Representation
//!
//! A [`Formula`] is a flat table, every child before its parent and the root
//! last, so shared subformulas are stored once; admission, decision,
//! validation and destruction are loops, never recursion. A node the root does
//! not reach has no meaning and is never cited. Indices and sizes cross the
//! API as the newtypes [`Point`], [`PointCount`], [`Variable`] and [`NodeId`].
//!
//! # References
//!
//! - Maximilian Schönlank, Andreas Nuyts and Dominique Devriese. "Towards
//!   `FaceTT`: a generalization of intensional type systems with glue". TYPES
//!   2026, abstract 42 and slides — the shape parameter `ft`, face theories
//!   over `⊤`, `⊥`, `∧`, `∨`, and decidable atomic entailment as the
//!   algorithmic assumption.
//! - Ambrus Kaposi and Szumi Xie. "Second-Order Generalised Algebraic Theories:
//!   Signatures and First-Order Semantics". FSCD 2024,
//!   `doi:10.4230/LIPIcs.FSCD.2024.10` — the structural theory of signatures
//!   (Definition 13), whose substitution gives every representable sort its
//!   diagonal.
//! - Robert Rose and Daniel R. Licata. "Complexity of Cubical Cofibration
//!   Logics I: coNP-Complete Examples". TYPES 2024,
//!   `doi:10.4230/LIPIcs.TYPES.2024.9` — the coNP bar for the composite
//!   language.
//! - Thorsten Altenkirch, Yorgo Chamoun, Ambrus Kaposi and Michael Shulman.
//!   "Internal Parametricity, without an Interval". POPL 2024,
//!   `doi:10.1145/3632920` — bridges as a local theory without an interval.
//! - Cyril Cohen, Thierry Coquand, Simon Huber and Anders Mörtberg. "Cubical
//!   Type Theory: a constructive interpretation of the univalence axiom". TYPES
//!   2015, `doi:10.4230/LIPIcs.TYPES.2015.5` — the interval, its face lattice
//!   and Glue, the alternative not taken.
//!
//! [`FaceTT`]: https://types2026.cse.chalmers.se/abstracts/42.pdf
//! [Kaposi–Xie]: https://doi.org/10.4230/LIPIcs.FSCD.2024.10
//! [Rose–Licata]: https://doi.org/10.4230/LIPIcs.TYPES.2024.9
//! [ACKS]: https://doi.org/10.1145/3632920
//! [CCHM]: https://doi.org/10.4230/LIPIcs.TYPES.2015.5

// Module documentation that predates the shape lint: 5 headings outside the
// vocabulary, 1 decision record and 2 duplicated paragraphs. Each allow leaves
// with the rewrite that clears its count.
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    allow(
        module_doc_heading,
        doc_decision_record,
        module_doc_duplication,
        reason = "module documentation that predates the shape lint"
    )
)]
#![no_std]

extern crate alloc;

/// Defines a transparent newtype over one primitive with `From` conversions
/// both ways.
macro_rules! wrapper {
    ($(#[$meta:meta])* $vis:vis struct $name:ident($raw:ty);) => {
        $(#[$meta])*
        #[repr(transparent)]
        $vis struct $name($raw);

        impl From<$raw> for $name
        {
            /// Wraps the primitive.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn from(value: $raw) -> Self
            {
                Self(value)
            }
        }

        impl From<$name> for $raw
        {
            /// Unwraps the primitive.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn from(value: $name) -> Self
            {
                value.0
            }
        }
    };
}

mod error;
mod finite;
mod formula;
mod index;
mod oracle;

pub use error::ShapeError;
pub use finite::Block;
pub use finite::Cofibration;
pub use finite::Inclusion;
pub use finite::Leg;
pub use finite::Membership;
pub use finite::SetOperation;
pub use finite::Subshape;
pub use finite::UnionSquare;
pub use formula::Formula;
pub use formula::Node;
pub use formula::Problem;
pub use index::NodeId;
pub use index::Point;
pub use index::PointCount;
pub use index::Variable;
pub use oracle::Citation;
pub use oracle::Countermodel;
pub use oracle::Derivation;
pub use oracle::Evidence;
pub use oracle::decide;
