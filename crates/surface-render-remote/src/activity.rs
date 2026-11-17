//! The activity of the hub's pool, as the render bus carries it: one row for
//! each core, and the totals row.
//!
//! The hub folds its work ledger once for each tick and sends a
//! [`PoolActivity`] when the tick changes it. A row holds the busy time of the
//! last cells of the core, one cell for each tick, and the kind of the task
//! that the core runs now. It also holds the busy time over the window, and
//! the lengths of the tasks that ended in the window at p50 and p99. The totals
//! row sums the cores, and its lengths are those of every task of the pool. A
//! renderer folds nothing: each number that it shows is a field here.
//!
//! # References
//!
//! - `vault:01a1c68b-1e9e-7942-aa36-b8d9096dec0e` — anchor: the engine surface,
//!   § engine-surface-activity: the columns of the activity pane.

use alloc::vec::Vec;

use crate::visual::Count;
use crate::visual::Samples;

/// The kind of a task that a core runs.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "camelCase"))]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum TaskKind
{
    /// A job that a check forks onto the pool.
    Fork,
    /// The kernel's replay of a declaration.
    Replay,
    /// The compilation of a declaration.
    Compile,
    /// The fetch of a chunk from the store.
    Fetch,
}

impl From<TaskKind> for &'static str
{
    /// The kind's name, as a face writes it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(kind: TaskKind) -> Self
    {
        match kind {
            TaskKind::Fork => "fork",
            TaskKind::Replay => "replay",
            TaskKind::Compile => "compile",
            TaskKind::Fetch => "fetch",
        }
    }
}

/// The lengths of the tasks that ended in the window, in nanoseconds: the
/// median and the 99th percentile.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Lengths
{
    /// The median length.
    pub p50: Count,
    /// The 99th percentile of the lengths.
    pub p99: Count,
}

/// The load of one core, or of the whole pool, over the window.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Load
{
    /// The busy time of each of the last cells of the window, in nanoseconds,
    /// the oldest first: one cell for each tick.
    pub occupancy: Samples,
    /// The busy time over the window, in nanoseconds.
    pub busy: Count,
    /// The lengths of the tasks that ended in the window; absent when no task
    /// ended in it.
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub lengths: Option<Lengths>,
}

/// The row of one core.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct CoreActivity
{
    /// The world of the last task of the core; absent before its first task.
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub world: Option<Count>,
    /// The core: the place of its ring in the ledger.
    pub core: Count,
    /// The kind of the task that the core runs now; absent while the core is
    /// idle.
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub now: Option<TaskKind>,
    /// The load of the core.
    pub load: Load,
}

/// The activity of the hub's pool at one tick: one row for each core, and the
/// totals row.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct PoolActivity
{
    /// The span of the window, in nanoseconds.
    pub window: Count,
    /// One row for each core, in the order of the cores.
    pub cores: Vec<CoreActivity>,
    /// The sum over the cores. Its lengths are those of every task of the
    /// pool.
    pub totals: Load,
}
