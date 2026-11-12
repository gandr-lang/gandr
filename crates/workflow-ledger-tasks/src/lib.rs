//! The ledger tasks of gandr's surface: the syntax ledger read off the
//! grammar, the exemplars that show each of its rows, the recovery sweep over
//! those exemplars, and the list and the show of the features ledger.
//!
//! The crate stands above `gandr-surface-dispatcher`. It reads the
//! dispatcher's composition, walk and pool, and no crate of the shipped
//! toolchain reads it. So an edit of a ledger task rebuilds this crate and its
//! binary alone. The binary `gandr-ledger` runs a [`LedgerTask`] for each of
//! its five verbs, and the task files run the binary. The `ledger` module
//! states how each ledger is built and checked.

// Module documentation that predates the shape lint, moved with the `ledger`
// module: 15 headings outside the vocabulary, 9 decision records, 4 issue
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

mod ledger;

pub use crate::ledger::ExemplarFault;
pub use crate::ledger::ExemplarFinding;
pub use crate::ledger::ExemplarReport;
pub use crate::ledger::LedgerFault;
pub use crate::ledger::LedgerRun;
pub use crate::ledger::LedgerTask;
pub use crate::ledger::RecoveryFinding;
pub use crate::ledger::RecoveryReport;
pub use crate::ledger::RecoveryTally;
pub use crate::ledger::SyntaxLedger;
