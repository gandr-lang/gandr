//! Each declaration a settled source writes, measured in the kernel artifact
//! its component's admission exported, and in the tally of that admission.
//!
//! # A row is a segment of the kernel's artifact
//!
//! The kernel exports one artifact per component: its declarations in
//! admission order, each a segment over one maximally shared subterm table.
//! A row reads three sizes off that artifact for one declaration the source
//! writes: its segment's bytes, the table entries its segment adds and the
//! expanded work of its roots. The entries are its shared size, a subterm an
//! earlier segment holds counted there. The expanded work is its unshared
//! size, the tree its roots stand for. A reference to an earlier declaration
//! is one node, so a row measures the declaration as written over the
//! definitions it names, never unfolded.
//!
//! A row also reads what the admission tallied: the census the kernel's check
//! charged, goal by goal, and the time the kernel took to admit it. The census
//! counts each goal the check expanded, each its memo recalled and each an
//! earlier admission's kept outcome answered. A declaration a recorded verdict
//! admitted ran no check, and its row says so rather than counting nothing. A
//! resumed declaration carries the tally of the run that admitted it.
//!
//! # A component's checks are jobs of one schedule
//!
//! Each declaration that the kernel admitted is one job. Its references to
//! the entries that the same admission added are its dependences, and the
//! time of its admission is its cost. [`CheckSchedule`] reads from them the
//! critical path that no width beats, the bound of a release in slice order
//! and the chain of the critical path
//! ([`gandr_core_fork::Dependences::bound`]).
//! An entry that the admission resumed or that the prelude holds is committed
//! before the first job, so no job waits on it.
//!
//! # Measuring reads and never checks
//!
//! [`measure`] decodes the artifact the admission already exported and
//! changes no verdict. It reads each declaration at the position its
//! admission recorded, which only a walk asked to measure records
//! ([`crate::Walk::measuring`]), so a check that measures nothing records,
//! times and decodes nothing more.
//!
//! # References
//!
//! - `vault:01a18572-6e13-7412-bc74-aa6a24d157c4` — background: Example 1.4 and
//!   § 6 give the artifact sizes in bytes that a row's bytes stand beside.
//! - `vault:01a178aa-655f-72f2-97ee-298c0647e1e5` — background: the sharing
//!   ratio of iterated composites grows with dimension, which a row's shared
//!   and unshared sizes measure.
//! - `vault:01a051fd-25fd-7f24-a5d4-a72eca18a687` — lineage: the sharing
//!   format's one table per artifact and its expanded-work budget, the shared
//!   and unshared sizes a row reads.
//! - `vault:01a178aa-6917-7983-b5cd-86e2af86b3ec` — newest: the checks of one
//!   environment run over the dependence graph of their supports, and the
//!   critical path bounds the wall time at every width. [`CheckSchedule`] reads
//!   that bound before the schedule runs.

use alloc::string::String;
use alloc::vec::Vec;
use core::time::Duration;

use anodized::spec;
use gandr_core_checker::bridge;
use gandr_core_checker::bridge::AdmissionCost;
use gandr_core_fork::Bound;
use gandr_core_fork::Dependence;
use gandr_core_fork::Dependences;
use gandr_kernel_core::ExpansionCensus;
use gandr_kernel_core::speculation::Rollbacks;
use gandr_kernel_core::speculation::Speculation;
use gandr_kernel_core::tallied;
use gandr_kernel_term::ByteCount;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DecodeError;
use gandr_kernel_term::ExpandedWork;
use gandr_kernel_term::TableEntryCount;
use gandr_kernel_term::decode;
use gandr_kernel_term::decode_measured;
use gandr_surface_lowering::SurfaceName;
use quenchant_shape::shape::Maybe;

use crate::compose::Composed;

/// One declaration a source writes, measured in its component's kernel
/// artifact and in its admission's tally.
///
/// # Specification
/// - requires: built by [`measure`].
/// - ensures: the declaration's name, its segment's bytes, the table entries
///   its segment adds, the expanded work of its roots, the census its check
///   charged and the time its admission took.
/// - panics: none.
/// - executable: none — the fields are private and set only by [`measure`],
///   whose specification states them.
///
/// # Adequacy
/// - hypothesis: L2 — as [`measure`]'s.
/// - witness: `tests::measure::a_source_measures_the_declarations_it_writes_and_none_it_imports`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Measure<'source>
{
    /// The declaration's name, as the source spells it.
    name: SurfaceName<'source>,
    /// The bytes its segment takes.
    bytes: ByteCount,
    /// The table entries its segment adds: its shared size.
    shared: TableEntryCount,
    /// The expanded work of its roots: its unshared size.
    unshared: ExpandedWork,
    /// What the kernel's check of it charged, goal by goal, or why no check
    /// was tallied.
    census: Maybe<ExpansionCensus, tallied::Absent>,
    /// What the kernel spent to admit it, or why no time was read.
    took: AdmissionCost,
}

impl<'source> Measure<'source>
{
    /// The declaration's name, as the source spells it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn name(&self) -> SurfaceName<'source>
    {
        self.name
    }

    /// The bytes the declaration's segment takes in the kernel's artifact.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn bytes(&self) -> ByteCount
    {
        self.bytes
    }

    /// The table entries the declaration's segment adds: its shared size.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn shared(&self) -> TableEntryCount
    {
        self.shared
    }

    /// The expanded work of the declaration's roots: its unshared size.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn unshared(&self) -> ExpandedWork
    {
        self.unshared
    }

    /// What the kernel's check of the declaration charged: each goal it
    /// expanded, each its memo recalled and each an earlier admission's kept
    /// outcome answered. A declaration a recorded verdict admitted ran no
    /// check here.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn census(&self) -> Maybe<ExpansionCensus, tallied::Absent>
    {
        self.census
    }

    /// What the kernel spent to admit the declaration, or why no time was
    /// read.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn took(&self) -> AdmissionCost
    {
        self.took
    }
}

quenchant_shape::reason_enum! {
    /// Why a composition has no rows to measure.
    pub mod measured {
        /// The reason none is measured.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The lowering refused the source as a whole, so it declares
            /// nothing.
            Refused,
            /// The module's admission has not run, so no artifact exists.
            Pending,
            /// The admission recorded no artifact positions: the walk was
            /// not asked to measure.
            Unpositioned,
            /// The admission read no clock, so its jobs carry no cost and
            /// it has no schedule.
            Untimed,
        }
    }
}

/// The schedule that the checks of one component's admission can reach.
///
/// Each declaration that the kernel admitted is a job, its references to
/// earlier jobs are its dependences, and the time of its admission is its
/// cost.
///
/// # Specification
/// - requires: built by [`CheckSchedule::of`].
/// - ensures: the jobs in kernel position order, their dependences by job, the
///   count of jobs that carry no time, the bound of their schedule, the
///   speculation group that the admission ran under and the count of its
///   rollbacks.
/// - panics: none.
/// - executable: none — the fields are private and set only by
///   [`CheckSchedule::of`], whose specification states them.
///
/// # Adequacy
/// - hypothesis: L2 — as [`CheckSchedule::of`]'s.
/// - witness: `tests::measure::a_component_s_schedule_waits_on_the_references_of_each_job`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CheckSchedule
{
    /// The kernel position of each job, ascending.
    jobs: Vec<ConstantIndex>,
    /// The dependences of the jobs, each by its place in `jobs`.
    dependences: Dependences,
    /// The kernel position of each job that carries no time, ascending, each
    /// at no cost: a member of a mutual block, which the kernel admits with
    /// its block.
    untimed: Vec<ConstantIndex>,
    /// What a schedule of the jobs can reach.
    bound: Bound,
    /// The speculation group that the admission ran under.
    speculation: Speculation,
    /// How many predictions the kernel's fold found wrong and set right.
    rollbacks: Rollbacks,
}

impl CheckSchedule
{
    /// The schedule of the declarations that `readmission` admitted, each
    /// after the ones that it resumed.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one job for each readmitted declaration after the resumed
    ///   ones whose outcome is a definition, an axiom or a nominal declaration,
    ///   at its kernel position, in position order. A job waits on each other
    ///   job at a position that the kernel's `Entries::waits_on` names for it.
    ///   Its cost is the time that its admission took, and nothing when no time
    ///   was read, which the untimed jobs name. The bound is
    ///   [`Dependences::bound`] over those dependences and costs. The group and
    ///   the rollbacks are the readmission's environment's.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — over a source whose definitions read each other in a
    ///   chain and beside it, a job waits on exactly the jobs that its
    ///   definition names, and the critical path covers the chain's costs.
    /// - witness: `tests::measure::a_component_s_schedule_waits_on_the_references_of_each_job`
    #[spec(ensures: |ret| {
        let jobs = ret.jobs.len();
        ret.untimed.len() <= jobs && jobs <= readmission.readmitted().len()
    })]
    #[must_use]
    pub(crate) fn of(readmission: &bridge::Readmission) -> Self
    {
        let environment = readmission.environment();
        let entries = environment.entries();
        let mut timed: Vec<(ConstantIndex, AdmissionCost)> = readmission
            .readmitted()
            .iter()
            .skip(usize::from(readmission.resumed()))
            .filter_map(|entry| match *entry.outcome() {
                bridge::Outcome::Data { admitted, .. }
                | bridge::Outcome::Defined { admitted, .. }
                | bridge::Outcome::Assumed { admitted, .. } => {
                    Some((admitted.position(), entry.took()))
                },
                bridge::Outcome::Marked(_)
                | bridge::Outcome::Suspended
                | bridge::Outcome::Static
                | bridge::Outcome::Refused(_)
                | bridge::Outcome::Rejected(_) => None,
            })
            .collect();
        timed.sort_unstable_by_key(|&(position, _)| position);
        let jobs: Vec<ConstantIndex> = timed.iter().map(|&(position, _)| position).collect();
        let mut untimed = Vec::new();
        let costs: Vec<Duration> = timed
            .iter()
            .map(|&(position, took)| match took {
                Maybe::Present(spent) => spent.wall(),
                Maybe::Absent(_) => {
                    untimed.push(position);
                    Duration::ZERO
                },
            })
            .collect();
        let held = &jobs;
        let dependences = Dependences::new(held.iter().enumerate().flat_map(|(after, &position)| {
            entries.waits_on(position).filter_map(move |reference| {
                held.binary_search(&reference)
                    .ok()
                    .filter(|&before| before < after)
                    .map(|before| Dependence { before, after })
            })
        }))
        // Each edge waits on an earlier job, so none is backward.
        .unwrap_or_default();
        let bound = dependences.bound(&costs);
        Self {
            jobs,
            dependences,
            untimed,
            bound,
            speculation: environment.speculation(),
            rollbacks: environment.rollbacks(),
        }
    }

    /// The kernel position of each job, ascending.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn jobs(&self) -> &[ConstantIndex]
    {
        &self.jobs
    }

    /// The dependences of the jobs, each by its place in [`Self::jobs`].
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn dependences(&self) -> &Dependences
    {
        &self.dependences
    }

    /// The kernel position of each job that carries no time, ascending, each
    /// counted at no cost.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn untimed(&self) -> &[ConstantIndex]
    {
        &self.untimed
    }

    /// What a schedule of the jobs can reach: the serial cost, the critical
    /// path and the bound of the release in slice order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn bound(&self) -> &Bound
    {
        &self.bound
    }

    /// The speculation group that the admission ran under.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn speculation(&self) -> Speculation
    {
        self.speculation
    }

    /// How many predictions the kernel's fold found wrong and set right.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn rollbacks(&self) -> Rollbacks
    {
        self.rollbacks
    }

    /// The kernel position of each job on the critical path, in order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn chain(&self) -> impl Iterator<Item = ConstantIndex> + '_
    {
        self.bound
            .chain()
            .iter()
            .filter_map(|&item| self.jobs.get(usize::from(item)).copied())
    }
}

/// Measure each declaration `composed` writes in its component's kernel
/// artifact.
///
/// # Specification
/// - requires: nothing.
/// - ensures: absent as [`measured::Absent::Refused`] for a source refused as a
///   whole, as [`measured::Absent::Pending`] before its admission ran, and as
///   [`measured::Absent::Unpositioned`] when its admission recorded no
///   positions. Otherwise one row per declaration the source's report names
///   that crossed into the kernel, in the report's order, read at the artifact
///   position the admission gave it: its name, its segment's bytes, the table
///   entries its segment adds, the expanded work of its roots, the census the
///   kernel's check of it charged and the time its admission took. No row names
///   a declaration of the source's import closure.
/// - provides: the sizes and the tally `gandr check --measure` prints for each
///   declaration.
/// - fails: [`DecodeError`] when the exported artifact does not decode, which
///   the kernel's own export never meets.
/// - panics: none.
///
/// # Errors
/// [`DecodeError`] from [`decode_measured`].
///
/// # Adequacy
/// - hypothesis: L2 — over `library/std/src/math`, whose `std.math.cylinder`
///   imports `std.math.path` and the prelude, each source's rows are the
///   declarations it writes, in order, and none its closure holds. Each row
///   reads the segment of the artifact's declaration of its name, which a row
///   read at its module position does not. A shared size never passes its
///   unshared size, which separates the two columns swapped. Each row's census
///   charges at least one goal and its admission is timed, which a row read
///   from an untimed or unchecked admission is not. A walk not asked to measure
///   answers that it recorded no positions, rather than no rows.
/// - witness: `tests::measure::a_source_measures_the_declarations_it_writes_and_none_it_imports`
#[inline]
#[spec(ensures: |ret| match (composed, ret.as_ref()) {
    (&Composed::Settled { ref report, .. }, Ok(&Maybe::Present(ref rows))) => rows.len() <= report.declarations().len(),
    (&Composed::Refused(_), Ok(&Maybe::Absent(measured::Absent::Refused)))
    | (&Composed::Settled { .. }, Ok(&Maybe::Absent(measured::Absent::Pending | measured::Absent::Unpositioned)) | Err(_)) => true,
    _ => false,
})]
pub fn measure<'source>(
    composed: &Composed<'source>
) -> Result<Maybe<Vec<Measure<'source>>, measured::Absent>, DecodeError>
{
    let Composed::Settled {
        ref report,
        ref kernel,
        ref positions,
        ..
    } = *composed
    else {
        return Ok(Maybe::Absent(measured::Absent::Refused));
    };
    let Maybe::Present(ref kernel) = *kernel
    else {
        return Ok(Maybe::Absent(measured::Absent::Pending));
    };
    let Maybe::Present(ref positions) = *positions
    else {
        return Ok(Maybe::Absent(measured::Absent::Unpositioned));
    };
    let (artifact, measures) = decode_measured(kernel.as_image())?;
    let layout = artifact.segments();
    let rows = report
        .declarations()
        .iter()
        .filter_map(|declaration| {
            let Maybe::Present(placed) = positions.placed(declaration.constant())
            else {
                return None;
            };
            let position = placed.position();
            let measure = measures.get(usize::from(position))?;
            let span = layout.declaration_segment(position)?;
            Some(Measure {
                name: declaration.name(),
                bytes: ByteCount::from(
                    usize::from(span.end).saturating_sub(usize::from(span.start)),
                ),
                shared: measure.entries(),
                unshared: measure.expanded_work(),
                census: placed.census(),
                took: placed.took(),
            })
        })
        .collect();
    Ok(Maybe::Present(rows))
}

/// The schedule that the checks of one source's component can reach, beside
/// the name of each job on its critical path.
///
/// # Specification
/// - requires: built by [`schedule`].
/// - ensures: the component's schedule, and the kernel position and the
///   structured name of each job on its chain, in chain order.
/// - panics: none.
/// - executable: none — the fields are private and set only by [`schedule`],
///   whose specification states them.
///
/// # Adequacy
/// - hypothesis: L2 — as [`schedule`]'s.
/// - witness: `tests::measure::a_component_s_schedule_waits_on_the_references_of_each_job`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ScheduleRow<'composed>
{
    /// The component's schedule.
    schedule: &'composed CheckSchedule,
    /// Each job on the critical path, in chain order: its kernel position and
    /// its structured name, its segments apart by `.`. The name is empty
    /// when the producer gave the declaration none.
    chain: Vec<(ConstantIndex, String)>,
}

impl<'composed> ScheduleRow<'composed>
{
    /// The component's schedule.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn schedule(&self) -> &'composed CheckSchedule
    {
        self.schedule
    }

    /// Each job on the critical path, in chain order: its kernel position and
    /// its structured name, its segments apart by `.`. The name is empty
    /// when the producer gave the declaration none.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn chain(&self) -> &[(ConstantIndex, String)]
    {
        &self.chain
    }
}

/// The schedule that the checks of `composed`'s component can reach.
///
/// # Specification
/// - requires: nothing.
/// - ensures: absent as [`measured::Absent::Refused`] for a source refused as a
///   whole, as [`measured::Absent::Pending`] before its admission ran, as
///   [`measured::Absent::Unpositioned`] when its admission recorded no
///   positions, and as [`measured::Absent::Untimed`] when it read no clock.
///   Otherwise the component's [`CheckSchedule`], and each job on its chain in
///   chain order: its kernel position and the structured name that the
///   component's artifact gives it, empty when it has none.
/// - provides: the line `gandr check --measure` prints after a source's rows.
/// - fails: [`DecodeError`] when the exported artifact does not decode, which
///   the kernel's own export never meets.
/// - panics: none.
///
/// # Errors
/// [`DecodeError`] from [`decode`].
///
/// # Adequacy
/// - hypothesis: L2 — over a source whose definitions read each other in a
///   chain and beside it, each chain name is a declaration of the artifact, one
///   for each job of the chain.
/// - witness: `tests::measure::a_component_s_schedule_waits_on_the_references_of_each_job`
#[inline]
#[spec(ensures: |ret| match (composed, ret.as_ref()) {
    (&Composed::Settled { .. }, Ok(&Maybe::Present(ref row))) => row.chain.len() == row.schedule.bound().chain().len(),
    (&Composed::Refused(_), Ok(&Maybe::Absent(measured::Absent::Refused)))
    | (&Composed::Settled { .. }, Ok(&Maybe::Absent(measured::Absent::Pending | measured::Absent::Unpositioned | measured::Absent::Untimed)) | Err(_)) => true,
    _ => false,
})]
pub fn schedule<'composed>(
    composed: &'composed Composed<'_>
) -> Result<Maybe<ScheduleRow<'composed>, measured::Absent>, DecodeError>
{
    let Composed::Settled {
        ref kernel,
        ref positions,
        ..
    } = *composed
    else {
        return Ok(Maybe::Absent(measured::Absent::Refused));
    };
    let Maybe::Present(ref kernel) = *kernel
    else {
        return Ok(Maybe::Absent(measured::Absent::Pending));
    };
    let Maybe::Present(ref positions) = *positions
    else {
        return Ok(Maybe::Absent(measured::Absent::Unpositioned));
    };
    let Maybe::Present(schedule) = positions.schedule()
    else {
        return Ok(Maybe::Absent(measured::Absent::Untimed));
    };
    let artifact = decode(kernel.as_image())?;
    let declarations = artifact.declarations();
    let chain = schedule
        .chain()
        .map(|position| {
            let mut name = String::new();
            if let Some(declaration) = declarations.get(usize::from(position)) {
                for (at, segment) in declaration
                    .declaration()
                    .name()
                    .segments()
                    .iter()
                    .enumerate()
                {
                    if at > 0 {
                        name.push('.');
                    }
                    name.push_str(segment.as_ref());
                }
            }
            (position, name)
        })
        .collect();
    Ok(Maybe::Present(ScheduleRow { schedule, chain }))
}
