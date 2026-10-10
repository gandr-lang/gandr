//! A finite face calculus and the endpoint-only affine bridge shape.
//!
//! # Shape theory
//!
//! The `ft` presentation has pseudotypes `Finite(m)` and `Bridge` (𝔹).
//! Finite carriers have decidable equality and decidable subshapes, presented
//! by a subset and its complement. Their operations are inclusions, meets,
//! unions and the outer pushout of two inclusions over their intersection.
//! These are operations on finite outer types, not colimits of a graphical
//! site. [`finite::UnionSquare`] records the four-block presentation.
//!
//! Bridge terms are variables and the endpoints 0 and 1. An affine context
//! map assigns each target coordinate an endpoint or a distinct source
//! coordinate; source coordinates may be discarded or permuted, never copied.
//! Thus context concatenation is a tensor, not a categorical product.
//! [`affine::AffineMap`] checks this condition, including on composition.
//!
//! Faces are `Top`, `Bottom`, `Endpoint(i, e)`, `Member(x, S)`, `And`, and
//! `Or`. There is no bridge equality `i = j`, reversal, connection, or
//! diagonal. Axioms are the bounded distributive lattice laws, disjoint
//! endpoints `(i = 0) ∧ (i = 1) = Bottom`, and finite membership interpreted by
//! the supplied subset. In particular, `(i = 0) ∨ (i = 1) = Top` is NOT an
//! axiom. Face assumptions may repeat a coordinate: propositional idempotence
//! is not contraction of shape substitutions.
//!
//! # Semantics and evidence
//!
//! A bridge coordinate has three observable cases: endpoint 0, endpoint 1,
//! or generic. Generic is an observation of a fresh coordinate, not a third
//! constant of 𝔹. Endpoint-only formulas distinguish no other cases. For any
//! ternary assignment, use distinct fresh variables for its generic entries;
//! this realizes it by an affine substitution. Conversely every affine
//! substitution induces such an assignment. Together with finite membership,
//! these assignments give a complete finite model for this face language.
//! They do not make 𝔹 a discrete three-point shape.
//!
//! The oracle prunes partial assignments when the premise is forced false or
//! the conclusion forced true. A positive derivation uses these two leaf
//! rules and exhaustive case analysis on one unassigned coordinate. Replay
//! checks every leaf and every case without invoking the oracle. A negative
//! result supplies a total assignment checked against both input formulas.
//! Exhausting a zero-point finite coordinate closes an empty context.
//!
//! This is a FaceTT-style parameter presentation. The published TYPES 2026
//! slides include shape equality and depict cartesian shape arities; they do
//! not establish an affine instantiation. The affine context discipline here
//! is explicit, and an embedding into `FaceTT` or a logical framework needs its
//! own structural argument.
//!
//! # Glue specification
//!
//! Given `Γ ⊢ A : U`, a well-formed face `φ`, and under `Γ, φ` a type
//! `T : U` and `f : T → A`, the specified former is
//! `Γ ⊢ Glue[φ ↦ (T, f)] A : U`, with judgmental restriction to `T` under
//! `φ` and `unglue : Glue[φ ↦ (T, f)] A → A` restricting to `f`; at
//! `Bottom`, Glue is `A`.
//! Here `f` must be the forward map of a checked `Path_U(T, A)` equivalence
//! certificate, including its inverse and inverse laws. This is the
//! equivalence-input reading used for CCHM fibrancy; `FaceTT`'s abstract also
//! describes `ParamDTT` Glue with an arbitrary function to obtain relatedness.
//! The certificate requirement deliberately restricts that latter reading:
//! this specification derives no bridge from an arbitrary uncertified map,
//! and asserts neither Kan fibrancy nor univalence. Glue is specified here,
//! not implemented as a type former. See the crate README for sources.

#![no_std]

extern crate alloc;

pub mod affine;
pub mod boundary;
pub mod finite;
pub mod formula;
pub mod oracle;
