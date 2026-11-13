//! **Speculation**, the policy of the release schedule: what a release behind
//! the cursor predicts of the earlier commits, in place of a wait for them.
//!
//! Each setting is one knob, and the group is one value. A setting off takes
//! the hold of the release in serial order for its read, and the group off is
//! that release. The fold checks each prediction at the cursor, in position
//! order, and sets a wrong one right. So at every setting each outcome, each
//! entry and each record equals the serial run's.
//!
//! The driver sets the group by the kind of run: on where a pool of more than
//! one thread runs the checks, and off for a serial run. The measure output
//! prints the group that a run ran under, and the count of its rollbacks.
//!
//! # References
//!
//! - gandr #3476 — the parallel replay, § "Speculation as a policy of the
//!   schedule": the group, its settings and its defaults; and the answer on the
//!   plan of the optimistic landing: the rank as a sixth setting, and the three
//!   reads of order as names that take the edge.

use core::fmt;

/// One setting of the group.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Setting
{
    /// The release waits for the earlier commits that its read reads.
    #[default]
    Off,
    /// The release predicts what its read reads, and the fold checks it.
    On,
}

impl fmt::Display for Setting
{
    /// `on` or `off`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        formatter: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        formatter.write_str(match *self {
            Self::Off => "off",
            Self::On => "on",
        })
    }
}

/// The settings of the three reads of order that a release makes of the
/// earlier releases.
///
/// No source of the corpus or of the standard library holds a release on
/// these reads. So each setting takes the hold of the release in serial
/// order, on and off alike, and the prediction of a read comes with the first
/// source that holds on it.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct OrderReads
{
    /// The generative count over the committed set at the release.
    pub generative: Setting,
    /// The name of a twin over the committed definitions at the release.
    pub twin: Setting,
    /// The atoms sealed in the committed set at the release.
    pub manifest: Setting,
}

/// The group: what a release behind the cursor predicts.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct Speculation
{
    /// The rank of a declaration staged with no rank: the rank past each
    /// outstanding reservation, as if each outstanding release admits.
    pub rank: Setting,
    /// The three reads of order.
    pub order: OrderReads,
}

impl Speculation
{
    /// Every setting off: the release in serial order.
    pub const OFF: Self = Self {
        rank: Setting::Off,
        order: OrderReads {
            generative: Setting::Off,
            twin: Setting::Off,
            manifest: Setting::Off,
        },
    };
    /// Every setting on.
    pub const ON: Self = Self {
        rank: Setting::On,
        order: OrderReads {
            generative: Setting::On,
            twin: Setting::On,
            manifest: Setting::On,
        },
    };
}

impl fmt::Display for Speculation
{
    /// Each setting, by its name in the group:
    /// `rank on, order.generative on, order.twin on, order.manifest on`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        formatter: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(
            formatter,
            "rank {}, order.generative {}, order.twin {}, order.manifest {}",
            self.rank, self.order.generative, self.order.twin, self.order.manifest
        )
    }
}

/// How many predictions the fold found wrong and set right.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct Rollbacks(usize);

impl Rollbacks
{
    /// No rollback.
    pub const NONE: Self = Self(0);

    /// One rollback more.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn and_one(self) -> Self
    {
        Self(self.0.saturating_add(1))
    }
}

impl From<Rollbacks> for usize
{
    /// The count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(rollbacks: Rollbacks) -> Self
    {
        rollbacks.0
    }
}

impl fmt::Display for Rollbacks
{
    /// The count, in decimal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        formatter: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(formatter, "{}", self.0)
    }
}
