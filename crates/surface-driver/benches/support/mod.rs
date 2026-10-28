//! What the benchmark series share: a corpus path from the driver's manifest
//! directory, and a check that visits every step of its walk.

use core::ops::ControlFlow;
use std::path::PathBuf;

use gandr_surface_dispatcher::Goals;
use gandr_surface_dispatcher::HostGrant;
use gandr_surface_dispatcher::Invocation;
use gandr_surface_dispatcher::Lints;
use gandr_surface_dispatcher::Outcome;
use gandr_surface_dispatcher::Pool;
use gandr_surface_dispatcher::Width;

/// The path of a corpus source from the driver's manifest directory.
///
/// # Specification
/// trivial.
pub(crate) fn corpus(relative: &str) -> PathBuf
{
    std::fs::canonicalize(PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(relative))
        .expect("the corpus source exists")
}

/// Check `paths` and their closures, visiting every step of the walk.
///
/// # Specification
/// trivial.
pub(crate) fn check(paths: Vec<PathBuf>)
{
    let Outcome::Run { walk, width, .. } = gandr_surface_dispatcher::dispatch(Invocation::Check {
        goals: Goals::Gated,
        lints: Lints::default(),
        grant: HostGrant::UNBOUNDED,
        paths,
        width: Width::SERIAL,
    })
    else {
        panic!("check dispatches a walk");
    };
    let ControlFlow::Continue(report) =
        walk.visit(&Pool::new(width), |_step| ControlFlow::<()>::Continue(()))
    else {
        panic!("the visitor never stops the walk");
    };
    core::hint::black_box(report);
}
