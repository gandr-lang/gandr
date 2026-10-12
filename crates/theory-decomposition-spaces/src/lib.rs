//! Certificate algebra: sequential composition and bounded backward pathway
//! queries.
//!
//! The directed gate reads recorded cell support at the left certificate's
//! join. Its verdict is presentation-sensitive; an admitted graft preserves the
//! replay boundary. Pathway acceptance is relative to the shift guard.
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
