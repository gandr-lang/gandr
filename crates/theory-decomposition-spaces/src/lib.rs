//! Certificate algebra: sequential composition and bounded backward pathway
//! queries.
//!
//! The directed gate reads recorded cell support at the left certificate's
//! join. Its verdict is presentation-sensitive; an admitted graft preserves the
//! replay boundary. Pathway acceptance is relative to the shift guard.
//!
//! # Boundaries
//!
//! The algebra is a 2-Segal set, not a space. A certificate is a finite value
//! with a boundary, a composite is a value built from two, and the identity
//! of certificates is the replay relation of the certificates crate: decided
//! true or false, never a type whose elements are identifications.
//! [`compose_invertible`] descends to that relation; [`compose_directed`]'s
//! verdict reads the cells a certificate recorded, so it is a function of the
//! representative and not of its class. Unitality, which every 2-Segal space
//! has (Feller and others), is a hypothesis at the level of sets, so it is
//! discharged here rather than inherited: the unit on a seam is two empty
//! paths, and grafting it on either side is a unit up to replay.
//!
//! Univalence is never assumed in this crate. Reading the algebra as a
//! 2-Segal space, where unitality is free and the equivalence with augmented
//! stable double Segal objects (Bergner, Osorno, Ozornova, Rovelli and
//! Scheimbauer) carries no side condition, belongs above it, derived from `ua`
//! over the certified strata. Those strata rest on the decisions replay makes
//! here and in the kernel, so a step at the space level that changes what
//! this crate composes or admits would be circular.
//!
//! # References
//!
//! - Imma Gálvez-Carrillo, Joachim Kock and Andrew Tonks. “Decomposition
//!   Spaces, Incidence Algebras and Möbius Inversion I: Basic Theory.”
//!   _Advances in Mathematics_ 331 (2018), 952–1015.
//!   [doi:10.1016/j.aim.2018.03.016](https://doi.org/10.1016/j.aim.2018.03.016)
//!   — decomposition spaces and incidence coalgebras, not a rewriting
//!   implementation.
//! - Imma Gálvez-Carrillo, Joachim Kock and Andrew Tonks. “Decomposition Spaces
//!   in Combinatorics.” [arXiv:1612.09225v3, §2.5.5](https://arxiv.org/html/1612.09225v3#S2.SS5.Thmlemma5),
//!   2024 — the corrected planarity locator: ordered forests of planar trees
//!   give a decomposition space that is **monoidal but not symmetric
//!   monoidal**. This does not justify imposing planar order on a symmetric
//!   parallel-component interface. Ordering within a cell and permutation of
//!   independent components are separate choices here.
//! - Nicolas Behr and Joachim Kock. “Tracelet Hopf Algebras and Decomposition
//!   Spaces (Extended Abstract).” _EPTCS_ 372 (2022), 323–337.
//!   [doi:10.4204/EPTCS.372.23](https://doi.org/10.4204/EPTCS.372.23) — the
//!   tracelet composition and shift-quotient line. The implemented independence
//!   relation is the stricter guarded, trivial-overlap relation; this crate
//!   does not claim the paper's full quotient or a Hopf algebra.
//! - Matthew Feller, Richard Garner, Joachim Kock, May U. Proulx and Mark
//!   Weber. “Every 2-Segal Space Is Unital.” _Communications in Contemporary
//!   Mathematics_ 23 (2021), 2050055.
//!   [doi:10.1142/S0219199720500558](https://doi.org/10.1142/S0219199720500558).
//! - Julia E. Bergner, Angélica M. Osorno, Viktoriya Ozornova, Martina Rovelli
//!   and Claudia I. Scheimbauer. “2-Segal Objects and the Waldhausen
//!   Construction.” _Algebraic & Geometric Topology_ 21 (2021), 1267–1326.
//!   [doi:10.2140/agt.2021.21.1267](https://doi.org/10.2140/agt.2021.21.1267)
//!   — the edge between this layer and the doctrine layer.

// Module documentation that predates the shape lint: 7 headings outside the
// vocabulary. Each allow leaves with the rewrite that clears its count.
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    allow(
        module_doc_heading,
        reason = "module documentation that predates the shape lint"
    )
)]
#![no_std]

extern crate alloc;

mod boundary;
pub mod compose;
pub mod pathway;
pub mod transport;

pub use crate::boundary::PathwayCandidateBudget;
pub use crate::boundary::PathwayCandidateCount;
pub use crate::boundary::PathwayLength;
pub use crate::boundary::PathwayLengthBudget;
pub use crate::boundary::TargetEventCount;
pub use crate::compose::CompositionObstruction;
pub use crate::compose::compose_directed;
pub use crate::compose::compose_invertible;
