//! The checker's report that a pass assembles: each standing item's verdict
//! and parts seated from its checkpoint, each other item's from its decision.
//!
//! A keystroke that keeps no type table reads the module's report. A pass
//! that adopts each standing item and decides the rest has every part of that
//! report: the checkpoint of a standing item keeps its verdict, its failure,
//! its elaboration and its suspension as content, and a decided item's
//! decision holds them. So the pass gives the report, and the keystroke judges
//! no module whole.
//!
//! | Decision | Alternatives | Reversal |
//! | -------- | ------------ | -------- |
//! | The pass assembles the report from its adoptions and decisions | judge the module whole and take each changed item's verdict from it; take standing items inside the module run | a reader of the report needs a part that no checkpoint keeps |
//! | A part that does not seat leaves the pass with no report | decide the item again after its adoption | a part fails to seat at a measured rate |
//! | A refused item leaves the pass with no report | seat the refusal from its checkpoint, and take a decided refusal from its decision | a seated type keeps the written node that it stands for |
//!
//! A refusal names the types that the judgement meets. A type of a consulted
//! item stands in the pass's context as its adoption seated it: a node minted
//! apart from the written node that the whole judgement names. A diagnostic
//! locates each type that a refusal names by its origin, and a seated node has
//! none. So a refusal that the pass gives loses loci that the whole judgement
//! gives, and a revision that refuses an item is judged whole.

use alloc::collections::BTreeMap;
use alloc::sync::Arc;
use alloc::vec::Vec;

use gandr_core_checker::CheckingContext;
use gandr_core_checker::Declaration;
use gandr_core_checker::Given;
use gandr_core_checker::ModuleReport;
use gandr_core_checker::ModuleRun;
use gandr_core_checker::NestedElaboration;
use gandr_core_checker::Supported;
use gandr_core_checker::Taken;
use gandr_core_checker::Verdict;
use gandr_core_checker::elaboration::Suspension;
use gandr_core_checker::kept;
use gandr_core_checker::waits;
use gandr_kernel_term::ConstantIndex;
use quenchant_shape::shape::Maybe;

use crate::checkpoint::Judgement;
use crate::checkpoint::leading;
use crate::content::Encoded;
use crate::region::Layout;
use crate::report::ReportContent;
use crate::report::reported;
use crate::typing::Typing;

/// What a pass does with an item it does not adopt.
///
/// # Specification
/// trivial.
#[derive(Debug)]
pub enum Supply<'supply>
{
    /// The pass decides it.
    Decided,
    /// The pass takes its verdict and support from the revision's whole-module
    /// judgement, and decides it only where it cannot take them.
    Judged(Judgement<'supply>),
    /// The pass decides it, and assembles the checker's report of the
    /// revision into the reporting.
    Reported(&'supply mut Reporting),
}

quenchant_shape::reason_enum! {
    /// Why a reporting holds no report.
    pub mod assembled {
        /// The reason no report is held.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// No pass finished with the reporting: none ran, or it retired.
            Unpassed,
            /// The verdict or a part of an item did not seat, or the pass
            /// holds no suspension of a suspended item.
            Unseated,
            /// An item is refused, and its refusal names types that the pass
            /// holds apart from the written nodes that the whole judgement
            /// names.
            Refused,
            /// The pass started after leading items, and the reporting holds
            /// no run of them.
            Unled,
        }
    }
}

/// Where the report a pass assembled starts.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Started
{
    /// At the program's first item.
    Whole,
    /// After the leading items, continuing their run.
    After,
}

/// What a pass assembles of the checker's report of its revision, once a
/// caller asks for it.
///
/// # Specification
/// - executable: none — the reporting holds no program to certify the report
///   against; the corpus witness compares it with the whole judgement's.
///
/// # Adequacy
/// - hypothesis: L3 — over the corpus sources that the recheck sweeps visit,
///   the report that a pass assembles settles as the whole judgement of the
///   same revision settles, for each edit class.
/// - witness: `tests::incremental::a_reported_pass_assembles_the_report_of_the_whole_judgement_6620`
#[derive(Debug)]
pub struct Reporting
{
    /// The run of the leading items, which a pass after them continues.
    leading: Maybe<ModuleRun, leading::Absent>,
    /// The report that the last pass assembled, and where it starts.
    assembled: Maybe<(ModuleReport, Started), assembled::Absent>,
}

impl Reporting
{
    /// A reporting for a pass that starts at the program's first item, or
    /// after leading items whose run is `leading`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(leading: Maybe<ModuleRun, leading::Absent>) -> Self
    {
        Self {
            leading,
            assembled: Maybe::Absent(assembled::Absent::Unpassed),
        }
    }

    /// The report that the last pass assembled, and where it starts.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn into_assembled(self) -> Maybe<(ModuleReport, Started), assembled::Absent>
    {
        self.assembled
    }
}

/// One item's verdict and parts, as the pass assembles them into its report.
///
/// # Specification
/// trivial.
pub struct Part<'layout>
{
    /// The item's declaration.
    pub declaration: &'layout Declaration,
    /// The verdict.
    pub verdict: Verdict,
    /// The elaboration of the body's nested computations, or why none is kept.
    pub elaboration: Maybe<NestedElaboration, gandr_core_checker::elaborated::Absent>,
    /// What a suspended item waits on, or why none is kept.
    pub suspension: Maybe<Suspension, waits::Absent>,
}

/// One item's part, or why it has none.
pub type Assembled<'layout> = Maybe<Part<'layout>, assembled::Absent>;

/// The part of an adopted item: its verdict and parts seated in `context`'s
/// arena from its checkpoint's `typing` and `report`.
///
/// # Specification
/// - requires: `context` holds the item as its adoption entered it; `item` is
///   the item's encoding in `context`'s arena; `waiting` holds the suspension
///   that the adoption seated from `report`, if any.
/// - ensures: on success, the verdict that the typing gives with the type and
///   the body that the adoption entered, the elaboration seated from `report`,
///   and the suspension in `waiting`.
/// - fails: [`assembled::Absent::Refused`] for a refused item;
///   [`assembled::Absent::Unseated`] when the verdict or a part does not seat.
/// - panics: none.
/// - executable: none — a predicate would seat the parts again.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Reporting`].
/// - witness: `tests::incremental::a_reported_pass_assembles_the_report_of_the_whole_judgement_6620`
#[inline]
pub fn adopted<'layout>(
    context: &mut CheckingContext<'_>,
    (item, declaration, layout): (&Encoded, &'layout Declaration, &Layout),
    (typing, report): (&Typing, &Maybe<Arc<ReportContent>, reported::Absent>),
    waiting: &BTreeMap<ConstantIndex, Suspension>,
) -> Assembled<'layout>
{
    let constant = declaration.constant();
    let given = match *typing {
        Typing::Data => Given::Data,
        Typing::Checked { conversions } => Given::Checked(conversions),
        Typing::Synthesised { conversions, .. } => Given::Synthesised(conversions),
        Typing::Owed => Given::Owed,
        Typing::Suspended => Given::Suspended,
        Typing::Refused(_) => return Maybe::Absent(assembled::Absent::Refused),
    };
    let Maybe::Present(verdict) = given.verdict(context, declaration)
    else {
        return Maybe::Absent(assembled::Absent::Unseated);
    };
    let elaboration = match *report {
        Maybe::Present(ref report) if matches!(report.elaboration(), Maybe::Present(_)) => {
            let walk = item.sites.walk();
            match report.seat((context.arena_mut(), layout), (&walk, None)) {
                Ok((Maybe::Present(elaboration), _)) => Maybe::Present(elaboration),
                Ok((Maybe::Absent(_), _)) | Err(_) => {
                    return Maybe::Absent(assembled::Absent::Unseated);
                },
            }
        },
        Maybe::Present(_) | Maybe::Absent(_) => {
            Maybe::Absent(gandr_core_checker::elaborated::Absent::Unnested)
        },
    };
    let suspension = match verdict {
        Verdict::Suspended(_) => match waiting.get(&constant) {
            Some(suspension) => Maybe::Present(suspension.clone()),
            None => return Maybe::Absent(assembled::Absent::Unseated),
        },
        Verdict::Refused(_) => return Maybe::Absent(assembled::Absent::Refused),
        Verdict::Data
        | Verdict::Checked { .. }
        | Verdict::Synthesised { .. }
        | Verdict::Owed(_) => Maybe::Absent(waits::Absent::Unsuspended),
    };
    Maybe::Present(Part {
        declaration,
        verdict,
        elaboration,
        suspension,
    })
}

/// The part of a decided item: the verdict, the failure and the elaboration
/// that `supported` holds, and the suspension in `waiting`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: on success, the parts of `supported`, the suspension read from
///   `waiting`.
/// - fails: [`assembled::Absent::Refused`] for a refused decision;
///   [`assembled::Absent::Unseated`] for a suspended decision whose suspension
///   `waiting` does not hold.
/// - panics: none.
/// - executable: none — the clause restates the body.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Reporting`].
/// - witness: `tests::incremental::a_reported_pass_assembles_the_report_of_the_whole_judgement_6620`
#[inline]
pub fn decided<'layout>(
    declaration: &'layout Declaration,
    supported: &Supported,
    waiting: &BTreeMap<ConstantIndex, Suspension>,
) -> Assembled<'layout>
{
    let verdict = supported.verdict();
    let suspension = match verdict {
        Verdict::Suspended(_) => match waiting.get(&declaration.constant()) {
            Some(suspension) => Maybe::Present(suspension.clone()),
            None => return Maybe::Absent(assembled::Absent::Unseated),
        },
        Verdict::Refused(_) => return Maybe::Absent(assembled::Absent::Refused),
        Verdict::Data
        | Verdict::Checked { .. }
        | Verdict::Synthesised { .. }
        | Verdict::Owed(_) => Maybe::Absent(waits::Absent::Unsuspended),
    };
    Maybe::Present(Part {
        declaration,
        verdict,
        elaboration: supported.elaboration().map(NestedElaboration::clone),
        suspension,
    })
}

/// Assemble `parts` into the report that `reporting` holds: each part taken
/// in order into the run that the pass's start begins, which reads the rest
/// of the report from `context`.
///
/// # Specification
/// - requires: `parts` holds one part per item of the pass, in order, up to the
///   first absent part; `context` is the pass's context after its last item,
///   its blocks closed.
/// - ensures: the reporting holds the report of the run that takes each part,
///   started as `started` says, when every part is present and a pass after
///   leading items has their run; otherwise it holds the reason.
/// - panics: none.
/// - executable: none — the clause names the run that the body builds.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Reporting`].
/// - witness: `tests::incremental::a_reported_pass_assembles_the_report_of_the_whole_judgement_6620`
#[inline]
pub fn assemble(
    reporting: &mut Reporting,
    (parts, started): (Vec<Assembled<'_>>, Started),
    context: &mut CheckingContext<'_>,
)
{
    let mut run = match (started, &reporting.leading) {
        (Started::Whole, _) => ModuleRun::new(),
        (Started::After, &Maybe::Present(ref leading)) => leading.clone(),
        (Started::After, &Maybe::Absent(_)) => {
            reporting.assembled = Maybe::Absent(assembled::Absent::Unled);
            return;
        },
    };
    for part in parts {
        let Part {
            declaration,
            verdict,
            elaboration,
            suspension,
        } = match part {
            Maybe::Present(part) => part,
            Maybe::Absent(reason) => {
                reporting.assembled = Maybe::Absent(reason);
                return;
            },
        };
        run.take(
            declaration,
            Taken::new(
                verdict,
                (
                    Maybe::Absent(kept::Absent::Accepted),
                    elaboration,
                    suspension,
                ),
            ),
        );
    }
    reporting.assembled = Maybe::Present((run.finish(context), started));
}
