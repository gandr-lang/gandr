//! The certified kernel's **level oracle**: the universe-level algebra over
//! zero, level variables, successor and binary maximum, held in
//! always-canonical form, with an order oracle that returns checkable evidence
//! in both directions.
//!
//! The crate holds **levels only** — no terms, no types, and not even the
//! universe rule, which is one call into [`Level::lt`] and belongs to the
//! kernel proper. It is `no_std` over `core` and `alloc`, the sharpest form of
//! the trusted base's dependency wall, and depends on no other crate.
//!
//! # The algebra and its canonical form
//!
//! A level is a term over zero, level variables, successor and binary maximum,
//! interpreted over the naturals. Every such term is semantically a finite join
//! `max(c, x_1 + o_1, …, x_k + o_k)` of a constant part and per-variable
//! offsets, and that shape — dominated components removed, atoms keyed by
//! variable — is a **sorted canonical form**: two levels denote the same
//! function of their variables exactly when their canonical forms are
//! identical. [`Level`] *is* that canonical form, and the smart constructors
//! maintain it, so a non-canonical level is unrepresentable rather than merely
//! rejected.
//!
//! # The order oracle and its evidence
//!
//! `l ≤ m` over all valuations is decided by **domination**: every atom of `l`
//! must be dominated by a same-variable atom of `m`, and `l`'s constant part by
//! `m`'s value at the zero valuation. The oracle returns checkable evidence in
//! both directions — a [`LeqWitness`] pairing each left atom with its
//! dominating bound, or a [`LeqRefutation`] carrying a concrete
//! counter-valuation — and [`validate_witness`] and [`validate_refutation`]
//! check either against the two levels. Trust concentrates in the validators,
//! so the decision procedure is self-incriminating under mutation.
//!
//! # The landmark poset and entailment
//!
//! A fixed, declared set of order constraints over level variables — the
//! **landmark poset** — is admitted by loop-checking, which is a dichotomy with
//! evidence on both sides: [`LandmarkPoset::admit`] returns either an admitted
//! poset carrying a [`ConsistencyWitness`], an explicit homomorphism into `ℕ`
//! checked by evaluating every constraint under it, or a [`LoopWitness`], a
//! replayable pumping derivation showing no such homomorphism can exist.
//! Entailment under an admitted poset —
//! [`LandmarkPoset::entails_leq_with_evidence`] and
//! [`LandmarkPoset::entails_lt_with_evidence`] — returns a forward-derivation
//! [`EntailmentWitness`] or an [`EntailmentCountermodel`], each with its
//! validator.
//!
//! Declared constraints are **variable-only**, and query constants ride a
//! pinned bottom generator internal to the encoding; the landmark-poset module
//! carries the soundness argument. With no constraints declared, entailment
//! agrees with the free-fragment oracle on every input, which the property
//! differential pins.
//!
//! # What this crate refuses to hold
//!
//! Level inference and unification, generalization, displacement, constraint
//! hypotheses beyond the declared landmark poset, `imax`, and cumulativity are
//! exclusions of the stratification design rather than unbuilt steps.
//!
//! The named ideas and their primary references are in this crate's
//! `README.md`.

#![no_std]

extern crate alloc;

mod entail;
mod horn;
mod level;
mod order;
mod poset;

pub use crate::entail::Entailment;
pub use crate::entail::EntailmentCountermodel;
pub use crate::entail::EntailmentHolds;
pub use crate::entail::EntailmentWitness;
pub use crate::entail::validate_entailment_countermodel;
pub use crate::entail::validate_entailment_witness;
pub use crate::horn::ClauseIndex;
pub use crate::horn::HornOffset;
pub use crate::horn::HornShift;
pub use crate::horn::ModelIsInfinite;
pub use crate::horn::ModelValue;
pub use crate::level::Level;
pub use crate::level::LevelConstant;
pub use crate::level::LevelError;
pub use crate::level::LevelIsZero;
pub use crate::level::LevelOffset;
pub use crate::level::LevelValue;
pub use crate::level::LevelVar;
pub use crate::level::LevelVarIndex;
pub use crate::order::AtomBound;
pub use crate::order::ConstantBound;
pub use crate::order::EvidenceError;
pub use crate::order::LeqRefutation;
pub use crate::order::LeqWitness;
pub use crate::order::OrderComparison;
pub use crate::order::Strictness;
pub use crate::order::validate_refutation;
pub use crate::order::validate_witness;
pub use crate::poset::AdmissionOutcome;
pub use crate::poset::ConsistencyValue;
pub use crate::poset::ConsistencyWitness;
pub use crate::poset::ConstraintIndex;
pub use crate::poset::ConstraintRelation;
pub use crate::poset::Derivation;
pub use crate::poset::DerivationStep;
pub use crate::poset::EvidenceSubject;
pub use crate::poset::LandmarkConstraint;
pub use crate::poset::LandmarkPoset;
pub use crate::poset::LoopWitness;
pub use crate::poset::PosetError;
pub use crate::poset::PosetEvidenceError;
pub use crate::poset::validate_consistency;
pub use crate::poset::validate_loop_witness;
