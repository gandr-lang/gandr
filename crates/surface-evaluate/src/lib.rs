//! The run stage of gandr: each run of a checked module's program, on the
//! native code the emitter patches or on its portable executor.
//!
//! The dispatcher builds a program for each module it settles, and holds
//! its data, its construction and its reads
//! (`gandr_surface_dispatcher::Program`). The runs stand here, above the
//! dispatcher. A [`Machine`] borrows the parts of a program a run reads and
//! runs it. [`Runs`] gives a caller the runs of a program by method, and
//! [`Evaluator`] is the engine the composition, the walk, the type table and
//! the run verb of the dispatcher take (`gandr_surface_dispatcher::Engine`).

// Module documentation that predates the shape lint and moves with the run
// stage: 6 headings outside the vocabulary, 1 decision record, 2 issue
// references and 3 budgets exceeded. Each allow leaves with the rewrite that
// clears its count.
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    allow(
        module_doc_heading,
        doc_decision_record,
        doc_issue_reference,
        module_doc_budget,
        reason = "module documentation that predates the shape lint"
    )
)]

extern crate alloc;

mod evaluate;

// The digest of a corpus walk the tests of one nextest run share (#5256),
// the dispatcher's integration tests' own module.
#[cfg(test)]
#[path = "../../surface-dispatcher/tests/digest.rs"]
mod digest;

pub use crate::evaluate::Engine;
pub use crate::evaluate::Evaluator;
pub use crate::evaluate::Machine;
pub use crate::evaluate::RealsAdapter;
pub use crate::evaluate::Runs;
pub use crate::evaluate::ScheduledRuns;
