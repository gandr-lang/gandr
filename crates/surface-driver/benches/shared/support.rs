//! What the benchmark series share: a corpus path from the driver's manifest
//! directory, the width a series runs at, and a check that visits every step
//! of its walk under the policy that the driver installs for its width.

extern crate alloc;

use alloc::sync::Arc;
use core::num::NonZeroUsize;
use core::ops::ControlFlow;
use std::path::Path;
use std::path::PathBuf;

use gandr_surface_dispatcher::Goals;
use gandr_surface_dispatcher::HostGrant;
use gandr_surface_dispatcher::Invocation;
use gandr_surface_dispatcher::Lints;
use gandr_surface_dispatcher::Outcome;
use gandr_surface_dispatcher::Pool;
use gandr_surface_dispatcher::Threads;
use gandr_surface_dispatcher::Width;
use gandr_surface_evaluate::Evaluator;

/// The path of a corpus source from the driver's manifest directory.
///
/// # Specification
/// trivial.
pub fn corpus(relative: &Path) -> PathBuf
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
pub fn width() -> Width
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

/// Check `paths` and their closures at the series' width, visiting every
/// step of the walk.
///
/// # Specification
/// trivial.
pub fn check(paths: Vec<PathBuf>)
{
    check_at(paths, width());
}

/// Check `paths` and their closures at `width`, visiting every step of the
/// walk. The check installs what the driver installs for the width
/// ([`gandr_surface_dispatcher::install_width`]), so a series measures the
/// run that the driver makes. A process installs once, so the first check
/// wider than one thread sets the policy for each check after it.
///
/// # Specification
/// trivial.
pub fn check_at(
    paths: Vec<PathBuf>,
    width: Width,
)
{
    let Outcome::Run { walk, width, .. } = gandr_surface_dispatcher::dispatch(Invocation::Check {
        goals: Goals::Gated,
        lints: Lints::default(),
        grant: HostGrant::UNBOUNDED,
        paths,
        width,
    })
    else {
        panic!("check dispatches a walk");
    };
    let pool = Arc::new(Pool::new(width));
    gandr_surface_dispatcher::install_width(&pool, &walk);
    let ControlFlow::Continue(report) =
        walk.visit::<Evaluator, _, _>(&pool, |_step| ControlFlow::<()>::Continue(()))
    else {
        panic!("the visitor never stops the walk");
    };
    core::hint::black_box(report);
}
