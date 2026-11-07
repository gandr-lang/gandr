//! Insertion-only topological orders and offset-carrying feasible valuations.
//!
//! Standing graphs use bounded repair; one-shot callers use the batch traversal
//! in `gandr-theory-graphs`. Neither structure supports edge deletion.
//!
//! The potentials follow Ghrist and Riess. A feasible valuation is a fixed
//! point of the Tarski Laplacian of a sheaf of max-plus lattices on the graph.
//! Repair raises each potential along an improving path, the Tarski
//! iteration, until the least fixed point holds. A positive cycle is the
//! obstruction that no fixed point clears.
//! So its results hold in the order-theoretic form, in degree zero.
//!
//! # References
//!
//! - Robert Ghrist and Hans Riess. "Cellular Sheaves of Lattices and the Tarski
//!   Laplacian." _Homology, Homotopy and Applications_ 24(1) (2022), 325–345.
//!   `doi:10.4310/HHA.2022.v24.n1.a16` — global sections as the fixed points of
//!   the Tarski Laplacian, which the potential repair reaches.

// Module documentation that predates the shape lint: 4 headings outside the
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

pub mod maintenance;
pub mod potential;
mod slot;

pub use crate::maintenance::AcyclicityMaintenance;
pub use crate::maintenance::AdmittedEdgeCount;
pub use crate::maintenance::EdgeVerdict;
pub use crate::maintenance::InsertionCount;
pub use crate::maintenance::MaintenanceError;
pub use crate::maintenance::MaintenanceTelemetry;
pub use crate::maintenance::RefusalCount;
pub use crate::maintenance::RelocationCount;
pub use crate::maintenance::RepairCount;
pub use crate::maintenance::TopologicalOrderStatus;
pub use crate::maintenance::VisitCount;
pub use crate::potential::AdmittedConstraintCount;
pub use crate::potential::ConstraintVerdict;
pub use crate::potential::FeasibilityStatus;
pub use crate::potential::Offset;
pub use crate::potential::Potential;
pub use crate::potential::PotentialAbsence;
pub use crate::potential::PotentialError;
pub use crate::potential::PotentialMaintenance;
pub use crate::potential::PotentialTelemetry;
pub use crate::potential::RaiseCount;
pub use crate::potential::RefutationCount;
pub use crate::potential::RelaxationCount;
