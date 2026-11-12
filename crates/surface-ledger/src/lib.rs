//! The ledgers of gandr's own surface: the syntax ledger read off the
//! grammar, the exemplars that show each of its rows, the recovery sweep over
//! those exemplars, and the features ledger.
//!
//! The crate stands above `gandr-surface-dispatcher`. It reads the
//! dispatcher's composition, walk and pool, and the dispatcher reads nothing
//! of it. So an edit of a ledger rebuilds this crate and the driver, and never
//! the dispatcher or the crates above it. The driver runs a [`LedgerTask`] for
//! each `gandr ledger` verb. The `ledger` module states how each ledger is
//! built and checked.

extern crate alloc;

mod ledger;

pub use crate::ledger::Area;
pub use crate::ledger::ExemplarFault;
pub use crate::ledger::ExemplarFinding;
pub use crate::ledger::ExemplarReport;
pub use crate::ledger::Feature;
pub use crate::ledger::FeatureId;
pub use crate::ledger::FeatureLedger;
pub use crate::ledger::LedgerFault;
pub use crate::ledger::LedgerRun;
pub use crate::ledger::LedgerTask;
pub use crate::ledger::Malformed;
pub use crate::ledger::RecoveryFinding;
pub use crate::ledger::RecoveryReport;
pub use crate::ledger::RecoveryTally;
pub use crate::ledger::ShownFeature;
pub use crate::ledger::Status;
pub use crate::ledger::SyntaxLedger;
