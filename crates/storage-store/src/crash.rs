//! The named points before and after each durable step of a store's write,
//! where a crash test stops the writer.
//!
//! The variable [`VARIABLE`] names one point. The process reads it once, at
//! the first point it passes, and calls [`std::process::abort`] at the point it
//! names. An abort ends the process with no unwind, as a kill does, so the
//! store's files are left as that step left them.
//!
//! # Boundaries
//!
//! An abort keeps the kernel's page cache, so each write the process made
//! stands after it, synced or not. A write that a power loss drops before its
//! sync is therefore no case of this test. The IO layer's simulator, which
//! drops and tears writes from a seed, holds that case.

use std::sync::OnceLock;

/// The environment variable that names the point where a writer stops.
const VARIABLE: &str = "GANDR_STORE_CRASH_AT";

/// A point before or after one durable step of a store's write.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Point
{
    /// Before a naming syncs the segments that batches wrote to.
    ObjectsBefore,
    /// After a naming synced the segments that batches wrote to.
    ObjectsAfter,
    /// Before a fold's tree is written to the record plane.
    TreeBefore,
    /// After a fold's tree is synced in the record plane.
    TreeAfter,
    /// Before a fold's line is appended to the roots log.
    LogBefore,
    /// After a fold's line is synced in the roots log.
    LogAfter,
    /// Before a fold cuts the journal to a header over its tree.
    JournalBefore,
    /// After a fold's journal header is synced.
    JournalAfter,
}

impl Point
{
    /// The point `name` spells, as [`VARIABLE`] holds it.
    ///
    /// # Specification
    /// trivial.
    fn spelled(name: &std::ffi::OsStr) -> Stop
    {
        match name.to_str().unwrap_or_default() {
            "objects-before" => Stop::At(Self::ObjectsBefore),
            "objects-after" => Stop::At(Self::ObjectsAfter),
            "tree-before" => Stop::At(Self::TreeBefore),
            "tree-after" => Stop::At(Self::TreeAfter),
            "log-before" => Stop::At(Self::LogBefore),
            "log-after" => Stop::At(Self::LogAfter),
            "journal-before" => Stop::At(Self::JournalBefore),
            "journal-after" => Stop::At(Self::JournalAfter),
            _ => Stop::Never,
        }
    }
}

/// Where this process stops.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Stop
{
    /// At the point named.
    At(Point),
    /// Nowhere: the variable is unset or names no point.
    Never,
}

/// The point this process stops at, read once.
static STOP: OnceLock<Stop> = OnceLock::new();

/// Stop the process here when [`VARIABLE`] names `point`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: returns when the variable names another point or none; the
///   process aborts otherwise.
/// - provides: the stop a crash test takes at each step of a write.
/// - fails: none.
/// - panics: none.
/// - executable: none — an abort ends the process that checks it.
/// - intension: one load and one comparison after the first call.
///
/// # Adequacy
/// - hypothesis: L3 — a crash at each point of a fold leaves roots whose
///   objects load.
/// - witness: `tests::store::a_crash_after_each_step_of_a_fold_leaves_roots_that_load_7459`
pub fn passed(point: Point)
{
    let stop = STOP.get_or_init(|| {
        std::env::var_os(VARIABLE).map_or(Stop::Never, |name| Point::spelled(&name))
    });
    if *stop == Stop::At(point) {
        std::process::abort();
    }
}
