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
//!
//! # Compilation
//!
//! _Projection_ is the compiler: it takes a _choreography_, one program over
//! named _roles_, to an _endpoint_ per role, a closed program whose protocol
//! and crossing data are fixed, and the endpoint is the artifact. A _recipe_
//! names a program's endpoints. A _deployment_ binds each role to a world key,
//! an instance count and discovery, never entering an artifact's identity, so
//! one artifact runs as two processes or a fleet. A _local artifact_ is a
//! one-role choreography's endpoint: the degenerate case, and the only one
//! built today. A runtime component no type demands is a recipe policy, off by
//! default.
//!
//! `surface-evaluate` runs a checked source's `main` as a local artifact.
//! `runtime-emitter` holds an endpoint's code, and `runtime-net` holds its
//! network. Projection and the recipe have no crate yet.
//!
//! # References
//! - `vault:01a178aa-5497-7042-b9f4-56ce571601b1` — anchor: the build-out map,
//!   its seam test. A crate boundary encloses a strongly connected component.
//!   The run stage is one such component above the dispatcher, so it is one
//!   crate.

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
