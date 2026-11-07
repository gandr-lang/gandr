//! One law checker for ordered semirings and commutative rings: a carrier with
//! an order, a zero, a one, an addition and a multiplication, and a negation
//! for a ring.
//!
//! A grade, a weight, a distance and a cost are each a value of an ordered
//! semiring. The checker states the laws once: the semiring laws, the laws of
//! the order, and the monotonicity of both operations in the order. It
//! decides each law on every tuple of a finite carrier, and on every tuple of
//! the elements an instance generates when its carrier is infinite. A law
//! that fails returns the instance, the law and the elements that break it.
//!
//! An operation of an infinite carrier can leave the part that the machine
//! represents. The operation then refuses, and the checker reports the law as
//! undecided at those elements, apart from a broken law.
//!
//! Its laws hold in the order-theoretic form, a posemiring (Wood, Definitions
//! 4.1.1 and 4.1.2), and each instance computes exactly.
//!
//! A commutative ring takes the discrete order, so the sixteen laws hold for
//! it as for any ring. The ring checker adds the commutativity of the product
//! and the inverse of the sum. The exact amplitudes of Clifford+T circuits
//! are such a ring, `ℤ[1/√2, i]`, and the gates `H`, `S`, `T` and `CNOT` are
//! unitary matrices over it.
//!
//! # Items
//!
//! | Item | What it holds |
//! | ---- | ------------- |
//! | [`OrderedSemiring`], [`CommutativeRing`], [`Carrier`] | the signatures, and the elements a check reads |
//! | [`Law`], [`RingLaw`], [`check`], [`check_law`], [`check_ring`], [`check_ring_law`] | the sixteen laws and the two a ring adds, and the checkers of all of them or of one |
//! | [`Decided`], [`LawFailure`], [`Counterexample`] | what a check decided, and the instance, law and elements of a failure |
//! | [`Tropical`], [`MaxPlus`] | the max-plus semiring over exact dyadics with `−∞` |
//! | [`Lawvere`], [`Distance`] | the Lawvere quantale of extended non-negative dyadics, in the reverse order |
//! | [`Usage`], [`Usages`] | the usage semiring `{0, 1, ω}` that the core language's grades read, and its instance on the whole carrier |
//! | [`Amplitude`], [`RealAmplitude`], [`Coefficient`], [`Scale`] | the exact amplitudes `ℤ[1/√2, i]` and their real subring `ℤ[1/√2]`, each at its least scale |
//! | [`Amplitudes`], [`RealAmplitudes`] | the two rings under the discrete order, on the elements a check generates |
//! | [`Gate`], [`State`], [`QubitCount`], [`QubitIndex`], [`CircuitRefusal`] | the gates `H`, `S`, `T` and `CNOT` as unitary matrices, and the state vector of a register that a circuit acts on |
//!
//! # References
//!
//! - `vault:01a1aa2d-a69c-7030-91e0-337d68d88151` — exemplar: the ordered
//!   algebras of the frame, and the probe of their laws.
//! - `vault:01a178aa-6e2c-7720-a0bd-c5e1f9c4e08e` — exemplar: grades as counts,
//!   costs and distances, and the semirings that carry them.
//! - `Wood-2024-framework_semiringannotated_type_systems` — dependency: § 4.1,
//!   the posemiring laws of Definitions 4.1.1 and 4.1.2, which [`Law`] states,
//!   and the linearity posemiring of Example 4.1.3, which [`Usage`] is. Its
//!   order is the reverse of Wood's, so a sum of uses lies at or below a bound.
//!   James Wood, "A Framework for Semiring-Annotated Type Systems", doctoral
//!   thesis, University of Strathclyde, 2024.
//! - `Ahrens-2025-weighted_rewriting_semiring_semantics_abstract_reduction_systems`
//!   — dependency: § 2, the semiring of Definition 5 with the monotone partial
//!   order of footnote 3, which the laws state. No law states the complete
//!   lattice of Definition 7, which an infinite reduction needs. Emma Ahrens,
//!   Jan-Christoph Kassing, Jürgen Giesl and Joost-Pieter Katoen, "Weighted
//!   Rewriting: Semiring Semantics for Abstract Reduction Systems", 2025,
//!   `arXiv:2505.08496`.
//! - `Jeandel-2018-complete_axiomatisation_zxcalculus_clifford+t_quantum_mechanics`
//!   — dependency: § 8, Proposition 10: the Clifford+T fragment represents
//!   exactly the matrices over `D[e^{iπ/4}]`, `D = ℤ[1/2]`, the ring
//!   [`Amplitude`] holds. § 5.1 gives its canonical form over the dyadics.
//!   Emmanuel Jeandel, Simon Perdrix and Renaud Vilmart, "A Complete
//!   Axiomatisation of the ZX-Calculus for Clifford+T Quantum Mechanics",
//!   LICS 2018, `arXiv:1705.11151`.

#![no_std]

extern crate alloc;

mod amplitude;
mod gate;
mod instance;
mod law;
mod signature;
mod usage;

pub use amplitude::Amplitude;
pub use amplitude::Amplitudes;
pub use amplitude::Coefficient;
pub use amplitude::RealAmplitude;
pub use amplitude::RealAmplitudes;
pub use amplitude::Scale;
pub use gate::CircuitRefusal;
pub use gate::Gate;
pub use gate::QubitCount;
pub use gate::QubitIndex;
pub use gate::State;
pub use instance::Distance;
pub use instance::Lawvere;
pub use instance::MaxPlus;
pub use instance::NegativeDistance;
pub use instance::Tropical;
pub use law::Arity;
pub use law::Counterexample;
pub use law::Decided;
pub use law::Law;
pub use law::LawCount;
pub use law::LawFailure;
pub use law::Reach;
pub use law::RingLaw;
pub use law::TupleCount;
pub use law::check;
pub use law::check_law;
pub use law::check_ring;
pub use law::check_ring_law;
pub use signature::Carrier;
pub use signature::CommutativeRing;
pub use signature::Comparison;
pub use signature::InstanceName;
pub use signature::OrderedSemiring;
pub use signature::Outside;
pub use usage::Usage;
pub use usage::Usages;
