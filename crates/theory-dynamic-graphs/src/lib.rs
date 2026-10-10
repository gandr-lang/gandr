//! Insertion-only topological orders and offset-carrying feasible valuations.
//!
//! Standing graphs use bounded repair; one-shot callers use the batch traversal
//! in `gandr-theory-graphs`. Neither structure supports edge deletion.

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
