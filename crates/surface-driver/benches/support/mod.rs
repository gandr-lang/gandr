//! What the benchmark series share: a corpus path from the driver's manifest
//! directory, the width a series runs at, and a check that visits every step
//! of its walk.

use core::ops::ControlFlow;
use std::num::NonZeroUsize;
use std::path::PathBuf;

use gandr_surface_dispatcher::Goals;
use gandr_surface_dispatcher::HostGrant;
use gandr_surface_dispatcher::Invocation;
use gandr_surface_dispatcher::Lints;
use gandr_surface_dispatcher::Outcome;
use gandr_surface_dispatcher::Pool;
use gandr_surface_dispatcher::Threads;
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

/// The width that a series' walks and stagings run at: `--jobs <n>` on the
/// series' command line, which `cargo bench` passes after its `--`, or one
/// thread. The scaling account (`mise run bench:scaling`) runs the series at
/// each width of its curve, and CI's series run serial.
///
/// # Specification
/// trivial.
pub(crate) fn width() -> Width
{
    let mut arguments = std::env::args();
    while let Some(argument) = arguments.next() {
        if argument == "--jobs" {
            let threads = arguments
                .next()
                .and_then(|count| count.parse::<NonZeroUsize>().ok())
                .expect("--jobs takes a positive count of threads");
            return Width::Threads(Threads::from(threads));
        }
    }
    Width::SERIAL
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
        width: width(),
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
