//! The template memo: each harvest key's last template, drafted from before the
//! producer runs, and the controller that decides when a draft pays.
//!
//! A family whose key holds a template is walked against it before the
//! producer runs; a draft the kernel admits whole is the family's schema, and
//! anything else falls to the producer with the walk's time spent. The memo
//! keeps what each key last emitted: an admitted draft or producer template
//! replaces the old one, a family the producer leaves plain vacates it, and a
//! family the kernel refuses for its work bound keeps the old one, which then
//! drafts exactly the members it still matches.
//!
//! The controller weighs the time a draft spends against the producer's. Per
//! key it keeps the producer's last time, the last accepted and refused
//! drafts' times, and an acceptance average; across the memo it keeps the same
//! as averages over shares of the producer's time, and the cost of one new arm.
//! A key drafts while its acceptance clears the break-even its times give, and
//! the memo drafts while its own acceptance clears its own. A family declined
//! six times in a row, by its key or by the memo, drafts on the seventh, so no
//! estimate freezes.

use alloc::borrow::Cow;
use core::time::Duration;

use gandr_kernel_core::admission::Choice;
use gandr_kernel_core::admission::Proposal;
use gandr_kernel_core::admission::Refusal;
use gandr_kernel_core::admission::Row;
use gandr_kernel_core::admission::Schema;
use gandr_kernel_core::admission::Work;

use super::Analysis;
use super::Arena;
use super::Budget;
use super::Family;
use super::InheritanceCache;
use super::Maybe;
use super::MemberCount;
use super::MemberIndex;
use super::NodeCount;
use super::PriceGate;
use super::Production;
use super::StageError;
use super::Step;
use super::Template;
use super::TemplateRefusal;
use super::Vec;
use super::analyze;
use super::draft::ArmCount;
use super::draft::Coverage;
use super::draft::DraftKind;
use super::draft::Drafter;
use super::draft::Finished;
use super::draft::Miss;
use super::draft::PointCount;
use super::draft::Rebasing;
use super::draft::Revision;
use super::draft::Unfit;
use super::draft::Walk;
use super::draft::Widening;
use super::harvest::FamilyKey;
use super::spec;

#[cfg(test)]
pub(super) mod tests;

/// The weight of the newest sample in every average: the oMLX depth
/// controller's constant.
const ALPHA: Share = Share(0.08);

/// A family declined this many times in a row drafts instead: a probe duty of
/// one in seven.
const PROBE: DeclineCount = DeclineCount(7);

/// A monotone clock the caller supplies; the checker reads no clock of its
/// own.
pub trait Clock
{
    /// Time since a fixed origin.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: never less than an earlier reading of the same clock.
    /// - provides: every duration the memo measures, as a difference of two
    ///   readings, saturating at zero.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the reading is the implementation's; the memo
    ///   saturates a decreasing pair to zero rather than trusting it.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a stopped clock drafts every family of the edit-pair
    ///   corpus, and the cap reads the import time a widening measured.
    /// - witness: `template::tests::drafts_equal_fresh_runs_across_the_edit_traces`
    /// - witness: `template::memo::tests::the_fresh_arm_cap_withdraws_a_widening_that_costs_the_producers_time`
    fn now(&mut self) -> Duration;
}

/// Time spent on one family, by stage.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Spent
{
    /// Walking and finishing drafts, including a work-bound fallback's, and
    /// compacting a produced template the memo keeps.
    pub drafting: Duration,
    /// Analysis, production and proposal emission.
    pub producing: Duration,
    /// The kernel's schema check, binding and rows.
    pub admitting: Duration,
}

/// Where an admitted schema came from.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Origin
{
    /// The producer's own proposal.
    Produced,
    /// A draft from the memo's template.
    Drafted(DraftKind),
}

/// Why the controller did not draft a family whose key holds a template.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Decline
{
    /// The key's last accepted draft took at least the producer's time.
    NeverPays,
    /// The key's acceptance is at or below its break-even.
    BelowBreakEven,
    /// The memo's acceptance is at or below the memo's break-even.
    Off,
}

/// What the drafter did with one family.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Drafting
{
    /// The memo holds no template for the family's key.
    Unmemoized,
    /// The controller did not draft.
    Declined(Decline),
    /// A member missed the template.
    Missed(Miss),
    /// Widening by this many new arms would cost the producer's time.
    Capped(ArmCount),
    /// Every member matched, but the draft is not a fresh run's schema or does
    /// not pay.
    Unfit(Unfit),
    /// The kernel refused the drafted schema or a member's row.
    Refused(Refusal),
    /// Under the memoized price, one of the kernel's inheritance replays spent
    /// more than the producer's per-check allowance.
    ReplayBound(Work),
    /// The kernel admitted the draft and every member.
    Accepted(DraftKind),
}

/// What became of one family.
#[derive(Debug)]
pub enum FamilyAdmission
{
    /// The kernel admitted the schema and every member.
    Admitted
    {
        /// The kernel's checked schema.
        schema: Schema,
        /// Whose proposal it was.
        origin: Origin,
    },
    /// The kernel refused the producer's schema for its work bound; the memo's
    /// template, drafted exactly, admitted these members, and the rest replay
    /// plainly.
    Partial
    {
        /// The kernel's checked schema for the subfamily.
        schema: Schema,
        /// The admitted members, by index, in order.
        members: Vec<MemberIndex>,
    },
    /// The producer emitted no template; every member replays plainly.
    Plain(TemplateRefusal),
    /// The memoized producer's inheritance check exceeded this allowance.
    WorkBoundExceeded(NodeCount),
    /// The kernel refused the producer's schema or a member's row.
    Refused(Refusal),
}

/// One family's outcome, the drafter's part in it, and the time spent.
#[derive(Debug)]
pub struct FamilyReport
{
    /// What became of the family.
    pub admission: FamilyAdmission,
    /// What the drafter did.
    pub drafting: Drafting,
    /// Time spent, by stage.
    pub spent: Spent,
}

/// Why the memo holds no template for a family.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Unheld
{
    /// No family with this key was offered.
    Unseen,
    /// The key's last family emitted no template.
    Vacated,
}

/// A share of the producer's time, or an acceptance rate.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, PartialEq, PartialOrd)]
struct Share(f64);

/// How many families in a row were declined.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
struct DeclineCount(usize);

/// A duration measured at least once, or not yet.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
enum Estimate
{
    /// Nothing measured.
    #[default]
    Unmeasured,
    /// The last measurement.
    Measured(Duration),
}

/// An average sampled at least once, or not yet.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
enum Tracked
{
    /// Nothing sampled.
    #[default]
    Unsampled,
    /// The exponential average of every sample so far.
    Sampled(Share),
}

/// What the controller decided for one family.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Decision
{
    /// Draft the family.
    Draft,
    /// Send the family to the producer.
    Decline(Decline),
}

/// What the kernel made of one proposal and its rows.
#[derive(Debug)]
#[expect(
    clippy::large_enum_variant,
    reason = "one per offered proposal, matched at once; boxing the schema would allocate per \
              family to shrink the rare refusal"
)]
enum Judged
{
    /// The schema and every row were admitted.
    Admitted(Schema),
    /// The first refusal.
    Refused(Refusal),
}

/// One key's controller state.
#[derive(Clone, Copy, Debug)]
struct Controls
{
    /// The acceptance average, starting at one.
    acceptance: Share,
    /// The producer's last time.
    producing: Estimate,
    /// The last accepted draft's time.
    accepted: Estimate,
    /// The last refused draft's time.
    refused: Estimate,
    /// Families declined in a row.
    declined: DeclineCount,
}

/// The memo-wide controller state.
#[derive(Clone, Copy, Debug)]
struct Switch
{
    /// The acceptance average over every draft, starting at one.
    acceptance: Share,
    /// Accepted drafts' times as shares of their key's producer time.
    accepted: Tracked,
    /// Refused drafts' times as shares of their key's producer time.
    refused: Tracked,
    /// Families declined in a row while off.
    declined: DeclineCount,
    /// Seconds one new arm costs to import.
    arm: Tracked,
}

/// What the fresh-arm cap weighs: the key's producer time and the memo's cost
/// of one new arm.
#[derive(Clone, Copy, Debug)]
struct Cap
{
    /// The key's last producer time.
    producing: Estimate,
    /// Seconds one new arm costs to import.
    arm: Tracked,
}

/// A key's template, or the reason it holds none.
#[derive(Clone, Debug)]
#[expect(
    clippy::large_enum_variant,
    reason = "one per key, read by every draft of it; boxing the template would add an \
              indirection to every walk to shrink the few vacant slots"
)]
enum Held
{
    /// The last emitted template.
    Template(Template),
    /// The last family emitted none.
    Vacant,
}

/// One key's memory.
#[derive(Clone, Debug)]
struct Slot
{
    /// The harvest key.
    key: FamilyKey,
    /// The template a draft starts from.
    held: Held,
    /// The controller's state for this key.
    controls: Controls,
}

/// What a draft attempt produced before the kernel judged it.
#[expect(
    clippy::large_enum_variant,
    reason = "one per drafted family, matched at once; boxing the draft would allocate per \
              family to shrink the withdrawn reason"
)]
enum Attempt
{
    /// A draft fit to offer, and how it departs from the memo's template.
    Ready(super::draft::Draft, DraftKind),
    /// The drafter's reason for not offering one.
    Withdrawn(Drafting),
}

/// Each harvest key's last template, the controller's state, and the buffers
/// drafting and admission reuse, carried by the caller across programs.
///
/// # Specification
/// - provides: drafts from earlier programs' templates, each admitted only by
///   the kernel, and the producer for everything else.
/// - panics: none.
/// - executable: none — the memo's claims are stated on [`Memo::admit_family`].
#[derive(Clone, Debug)]
pub struct Memo
{
    /// One slot per key seen.
    // economy: keys are compared linearly, as harvest compares them; a family
    // count per program in the hundreds keeps the scan below the walk.
    slots: Vec<Slot>,
    /// The memo-wide controller state.
    switch: Switch,
    /// The drafter's reusable buffers.
    drafter: Drafter,
    /// The kernel's reusable row buffer.
    row: Row,
}

impl Default for Memo
{
    /// An empty memo whose controller drafts every family that has a
    /// template.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self {
            slots: Vec::new(),
            switch: Switch {
                acceptance: Share(1.0),
                accepted: Tracked::Unsampled,
                refused: Tracked::Unsampled,
                declined: DeclineCount(0),
                arm: Tracked::Unsampled,
            },
            drafter: Drafter::default(),
            row: Row::default(),
        }
    }
}

/// Move an average one step toward a sample.
///
/// # Specification
/// - ensures: the average moves by [`ALPHA`] of its distance to the sample, so
///   the result lies between the two.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — from 0.92, 27 refusals take an acceptance below the 0.1
///   break-even and one acceptance lifts it back; a wrong weight moves either
///   count.
/// - witness: `template::memo::tests::the_controller_drafts_while_drafting_pays_and_probes_when_it_stops`
#[spec(ensures: |output| (output.0 - average.0) * (output.0 - sample.0) <= 0.0_f64)]
fn toward(
    average: Share,
    sample: Share,
) -> Share
{
    Share(ALPHA.0 * (sample.0 - average.0) + average.0)
}

/// Fold a sample into an average that may not have one yet.
///
/// # Specification
/// - ensures: the first sample becomes the average; later ones move it by
///   [`ALPHA`] of their distance.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — a widening measured free samples a zero arm cost the cap
///   then reads; a memo's shares fix its break-even.
/// - witness: `template::memo::tests::the_fresh_arm_cap_withdraws_a_widening_that_costs_the_producers_time`
/// - witness: `template::memo::tests::the_controller_drafts_while_drafting_pays_and_probes_when_it_stops`
#[spec(ensures: |output| match (tracked, output) {
    (Tracked::Unsampled, Tracked::Sampled(average)) => average == sample,
    (Tracked::Sampled(old), Tracked::Sampled(average)) =>
        (average.0 - old.0) * (average.0 - sample.0) <= 0.0_f64,
    _ => false,
})]
fn sampled(
    tracked: Tracked,
    sample: Share,
) -> Tracked
{
    match tracked {
        | Tracked::Unsampled => Tracked::Sampled(sample),
        | Tracked::Sampled(average) => Tracked::Sampled(toward(average, sample)),
    }
}

/// One duration as a share of another.
///
/// # Specification
/// - ensures: `part / whole`; for a zero whole, zero when the part is zero too
///   (a clock that never advances makes every draft free) and infinite
///   otherwise (a draft against a producer measured at zero never pays).
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — a stopped clock drafts every family of the edit-pair
///   corpus, and measured shares move the break-even.
/// - witness: `template::tests::drafts_equal_fresh_runs_across_the_edit_traces`
/// - witness: `template::memo::tests::the_controller_drafts_while_drafting_pays_and_probes_when_it_stops`
#[spec(ensures: |output| if whole.is_zero() {
    output.0.to_bits() == if part.is_zero() { 0.0_f64 } else { f64::INFINITY }.to_bits()
} else {
    output.0.to_bits() == (part.as_secs_f64() / whole.as_secs_f64()).to_bits()
})]
fn share(
    part: Duration,
    whole: Duration,
) -> Share
{
    if whole.is_zero() {
        return Share(if part.is_zero() {
            0.0_f64
        }
        else {
            f64::INFINITY
        });
    }
    Share(part.as_secs_f64() / whole.as_secs_f64())
}

/// The acceptance above which drafting saves time, from accepted and refused
/// drafts' times as shares of the producer's.
///
/// # Specification
/// - ensures: absent when an accepted draft costs the producer's time or more;
///   otherwise $a^* = r / (1 - d + r)$ for accepted share $d$ and refused share
///   $r$, so an acceptance $a > a^*$ makes $a(1 - d) > (1 - a) r$: the expected
///   saving per family is positive.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — a scripted clock sets the shares on each side of the
///   bound, and the controller's draft or decline flips with it.
/// - witness: `template::memo::tests::the_controller_drafts_while_drafting_pays_and_probes_when_it_stops`
#[spec(ensures: |output| match output {
    Maybe::Present(bound) => accepted.0 < 1.0_f64 && bound.0 >= 0.0_f64 && bound.0 <= 1.0_f64,
    Maybe::Absent(Decline::NeverPays) => accepted.0 >= 1.0_f64 || accepted.0.is_nan(),
    Maybe::Absent(_) => false,
})]
fn break_even(
    accepted: Share,
    refused: Share,
) -> Maybe<Share, Decline>
{
    if accepted.0 < 1.0_f64 {
        Maybe::Present(Share(refused.0 / (1.0_f64 - accepted.0 + refused.0)))
    }
    else {
        Maybe::Absent(Decline::NeverPays)
    }
}

impl Switch
{
    /// Whether the memo-wide acceptance has fallen to its break-even.
    ///
    /// # Specification
    /// - ensures: `Off` exactly when both shares are sampled and the memo's
    ///   acceptance is at or below the break-even they give.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — refused drafts drive the acceptance below the
    ///   break-even and the controller stops drafting but for its probes.
    /// - witness: `template::memo::tests::the_controller_drafts_while_drafting_pays_and_probes_when_it_stops`
    #[spec(ensures: |output| matches!(output, Decision::Draft | Decision::Decline(Decline::Off)))]
    fn off(&self) -> Decision
    {
        let (Tracked::Sampled(accepted), Tracked::Sampled(refused)) = (self.accepted, self.refused)
        else {
            return Decision::Draft;
        };
        match break_even(accepted, refused) {
            | Maybe::Present(bound) if self.acceptance > bound => Decision::Draft,
            | _ => Decision::Decline(Decline::Off),
        }
    }
}

impl Controls
{
    /// A fresh key's state: acceptance one, nothing measured.
    ///
    /// # Specification
    /// trivial.
    const fn fresh() -> Self
    {
        Self {
            acceptance: Share(1.0),
            producing: Estimate::Unmeasured,
            accepted: Estimate::Unmeasured,
            refused: Estimate::Unmeasured,
            declined: DeclineCount(0),
        }
    }

    /// Whether this key's acceptance clears the break-even its times give.
    ///
    /// # Specification
    /// - ensures: a decline exactly when the producer's and both drafts' times
    ///   are measured and either an accepted draft took the producer's time or
    ///   more, or the acceptance is at or below the break-even.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a scripted clock sets the times on each side of the
    ///   bound, and the decision flips with it.
    /// - witness: `template::memo::tests::the_controller_drafts_while_drafting_pays_and_probes_when_it_stops`
    #[spec(ensures: |output| output != Decision::Decline(Decline::Off))]
    fn verdict(&self) -> Decision
    {
        let (
            Estimate::Measured(producing),
            Estimate::Measured(accepted),
            Estimate::Measured(refused),
        ) = (self.producing, self.accepted, self.refused)
        else {
            return Decision::Draft;
        };
        match break_even(share(accepted, producing), share(refused, producing)) {
            | Maybe::Present(bound) if self.acceptance > bound => Decision::Draft,
            | Maybe::Present(_) => Decision::Decline(Decline::BelowBreakEven),
            | Maybe::Absent(decline) => Decision::Decline(decline),
        }
    }

    /// Decide one family, counting declines toward the next probe.
    ///
    /// # Specification
    /// - ensures: `Draft` when neither the memo nor the key declines, or when
    ///   the decline would be the seventh in a row by whichever declines, which
    ///   then starts counting again; otherwise that decline, counted.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a key below its break-even and a memo switched off
    ///   each draft exactly every seventh family.
    /// - witness: `template::memo::tests::the_controller_drafts_while_drafting_pays_and_probes_when_it_stops`
    #[spec(ensures: |output| match output {
        Decision::Draft => true,
        Decision::Decline(Decline::Off) => switch.declined.0 > 0 && switch.declined < PROBE,
        Decision::Decline(_) => self.declined.0 > 0 && self.declined < PROBE,
    })]
    fn decide(
        &mut self,
        switch: &mut Switch,
    ) -> Decision
    {
        let (decline, declined) = match (switch.off(), self.verdict()) {
            | (Decision::Decline(decline), _) => (decline, &mut switch.declined),
            | (Decision::Draft, Decision::Decline(decline)) => (decline, &mut self.declined),
            | (Decision::Draft, Decision::Draft) => {
                self.declined = DeclineCount(0);
                return Decision::Draft;
            },
        };
        let count = DeclineCount(declined.0.saturating_add(1));
        if count >= PROBE {
            *declined = DeclineCount(0);
            return Decision::Draft;
        }
        *declined = count;
        Decision::Decline(decline)
    }

    /// Record a drafted family's outcome.
    ///
    /// # Specification
    /// - ensures: the key's and the memo's acceptance move toward one for an
    ///   accepted draft and zero otherwise; the key's last accepted or refused
    ///   time becomes `spent`; the memo's matching share moves toward `spent`
    ///   over the key's producer time when that is measured.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — accepted and refused drafts under a scripted clock
    ///   move the decision across the break-even.
    /// - witness: `template::memo::tests::the_controller_drafts_while_drafting_pays_and_probes_when_it_stops`
    #[spec(ensures: |()| match accepted {
        Acceptance::Accepted => self.accepted == Estimate::Measured(spent),
        Acceptance::Refused => self.refused == Estimate::Measured(spent),
    })]
    fn record(
        &mut self,
        switch: &mut Switch,
        accepted: Acceptance,
        spent: Duration,
    )
    {
        let sample = match accepted {
            | Acceptance::Accepted => Share(1.0),
            | Acceptance::Refused => Share(0.0),
        };
        self.acceptance = toward(self.acceptance, sample);
        switch.acceptance = toward(switch.acceptance, sample);
        let shares = match accepted {
            | Acceptance::Accepted => {
                self.accepted = Estimate::Measured(spent);
                &mut switch.accepted
            },
            | Acceptance::Refused => {
                self.refused = Estimate::Measured(spent);
                &mut switch.refused
            },
        };
        if let Estimate::Measured(producing) = self.producing
            && !producing.is_zero()
        {
            *shares = sampled(*shares, share(spent, producing));
        }
    }
}

/// Whether the kernel admitted a drafted family.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Acceptance
{
    /// Admitted whole.
    Accepted,
    /// Missed, withdrawn or refused.
    Refused,
}

/// The time since an earlier reading of a clock.
///
/// # Specification
/// - ensures: the difference of a fresh reading and `begun`, zero if the clock
///   went back.
/// - panics: none.
/// - executable: none — the fresh reading is the clock's.
///
/// # Adequacy
/// - hypothesis: L2 — a stopped clock reads every span as zero, which drafts
///   every family of the edit-pair corpus.
/// - witness: `template::tests::drafts_equal_fresh_runs_across_the_edit_traces`
fn since<C>(
    clock: &mut C,
    begun: Duration,
) -> Duration
where
    C: Clock,
{
    clock.now().saturating_sub(begun)
}

/// Offer a proposal and its rows to the kernel.
///
/// # Specification
/// - requires: one row per member, in order.
/// - ensures: `Admitted` exactly when the kernel checks the schema, binds the
///   members' arena and admits every member under its row; otherwise the first
///   refusal.
/// - fails: caller-budget exhaustion; Unbalanced for a row count that differs
///   from the member count.
/// - panics: none.
///
/// # Errors
/// Returns `StageError::Exhausted` or `StageError::Unbalanced`.
///
/// # Adequacy
/// - hypothesis: L2/L3 — drafts and producer proposals are admitted over the
///   edit-pair corpus, and a draft whose rows a corrupted template misreads is
///   refused.
/// - witness: `template::tests::drafts_equal_fresh_runs_across_the_edit_traces`
/// - witness: `template::tests::a_kernel_refused_draft_falls_back_to_the_producer`
#[spec(captures: [available = budget.0], ensures: |output| budget.0 <= available
    && (output.is_ok() || rows.len() != members.len() || budget.0 == 0))]
fn judge(
    arena: &Arena,
    members: &[Step],
    proposal: Proposal,
    rows: &[&[Choice]],
    row: &mut Row,
    budget: &mut Budget,
) -> Result<Judged, StageError>
{
    if rows.len() != members.len() {
        return Err(StageError::Unbalanced);
    }
    let refused = |refusal| match refusal {
        | Refusal::Syntax(StageError::Exhausted) => Err(StageError::Exhausted),
        | refusal => Ok(Judged::Refused(refusal)),
    };
    let schema = match Schema::check(proposal, budget) {
        | Ok(schema) => schema,
        | Err(refusal) => return refused(refusal),
    };
    {
        let consumer = match schema.bind(arena.clone(), budget) {
            | Ok(consumer) => consumer,
            | Err(refusal) => return refused(refusal),
        };
        for (step, choices) in members.iter().zip(rows) {
            let substitution = schema.substitute(schema.classifiers(), choices, row);
            let mut substitution = match substitution {
                | Ok(substitution) => substitution,
                | Err(refusal) => return refused(refusal),
            };
            if let Err(refusal) = substitution.admit(&consumer, *step, budget) {
                return refused(refusal);
            }
        }
    }
    Ok(Judged::Admitted(schema))
}

/// Split flat choices into one row per member.
///
/// # Specification
/// - ensures: `members` rows of `points` choices each, in order; empty rows for
///   a family without points.
/// - fails: Unbalanced when the choices do not divide so.
/// - panics: none.
///
/// # Errors
/// Returns `StageError::Unbalanced`.
///
/// # Adequacy
/// - hypothesis: L2 — drafts with points and without split into the rows the
///   kernel admits member by member.
/// - witness: `template::tests::drafts_equal_fresh_runs_across_the_edit_traces`
#[spec(ensures: |output| output.as_ref().ok().is_none_or(|rows| rows.len() == usize::from(members)))]
fn rows(
    choices: &[Choice],
    points: PointCount,
    members: MemberCount,
) -> Result<Vec<&[Choice]>, StageError>
{
    let (points, members) = (points.0, usize::from(members));
    if choices.len() != points.saturating_mul(members) {
        return Err(StageError::Unbalanced);
    }
    if points == 0 {
        return Ok(alloc::vec![&[][..]; members]);
    }
    Ok(choices.chunks(points).collect())
}

impl Template
{
    /// Walk, cap and finish a whole-family draft of this template.
    ///
    /// # Specification
    /// - ensures: `Ready` with a draft fit to offer, its kind; otherwise the
    ///   member miss, the fresh-arm cap or the departure that withdrew it. The
    ///   cap withdraws a draft adding $f > 0$ arms when the per-arm cost $c$
    ///   and the key's producer time $P$ are measured, $c > 0$ and $f c \ge P$;
    ///   the walk is spent by then, so only the import is weighed, and an
    ///   import measured free never caps. A finished widening samples $c$ into
    ///   the cap.
    /// - fails: a lookup error on either side; an intern refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `StageError::Unbalanced`, `StageError::UnknownTerm`,
    /// `StageError::UnknownType` or the graph's intern refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the edit-pair corpus drafts, widens and rebases, and
    ///   a measured per-arm cost withdraws a widening that would cost the
    ///   producer's time.
    /// - witness: `template::tests::drafts_equal_fresh_runs_across_the_edit_traces`
    /// - witness: `template::memo::tests::the_fresh_arm_cap_withdraws_a_widening_that_costs_the_producers_time`
    #[spec(ensures: |output| output.as_ref().ok().is_none_or(|attempt| match *attempt {
        Attempt::Ready(_, _) => true,
        Attempt::Withdrawn(drafting) => matches!(drafting,
            Drafting::Missed(_) | Drafting::Capped(_) | Drafting::Unfit(_)),
    }))]
    fn attempt<C>(
        &self,
        arena: &Arena,
        members: &[Step],
        gate: PriceGate,
        cap: &mut Cap,
        drafter: &mut Drafter,
        clock: &mut C,
    ) -> Result<Attempt, StageError>
    where
        C: Clock,
    {
        let walk = self.walk(
            arena,
            members,
            Widening::Widened,
            Rebasing::Allowed,
            drafter,
        )?;
        let (template, kind) = match walk {
            | Walk::Matched { template, kind } => (template, kind),
            | Walk::Missed(miss) => return Ok(Attempt::Withdrawn(Drafting::Missed(miss))),
        };
        let fresh = match kind {
            | DraftKind::Exact => ArmCount(0),
            | DraftKind::Widened(fresh) | DraftKind::Rebased(_, fresh) => fresh,
        };
        if let (Tracked::Sampled(arm), Estimate::Measured(producing)) = (cap.arm, cap.producing) {
            let count = u32::try_from(fresh.0).map_or(f64::INFINITY, f64::from);
            if fresh.0 > 0 && arm.0 > 0.0_f64 && count * arm.0 >= producing.as_secs_f64() {
                return Ok(Attempt::Withdrawn(Drafting::Capped(fresh)));
            }
        }
        let finished = template.finish(arena, members, Coverage::Whole, drafter, gate, clock)?;
        if let Ok(count) = u32::try_from(fresh.0)
            && count > 0
        {
            let each = drafter.importing().as_secs_f64() / f64::from(count);
            cap.arm = sampled(cap.arm, Share(each));
        }
        Ok(match finished {
            | Finished::Ready(mut draft) => {
                if let Cow::Owned(mut rebased) = template {
                    let revision =
                        core::mem::replace(&mut draft.revision, Revision::Kept(Vec::new()));
                    revision.apply(&mut rebased, draft.cost);
                    draft.revision = Revision::Replaced(rebased);
                }
                Attempt::Ready(draft, kind)
            },
            | Finished::Unfit(unfit) => Attempt::Withdrawn(Drafting::Unfit(unfit)),
        })
    }
}

impl Memo
{
    /// The template the memo holds for a family's key.
    ///
    /// # Specification
    /// - ensures: the template a draft of `family` starts from, or why there is
    ///   none.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — after every admitted family the held template's
    ///   proposal is compared with a fresh run's over the edit-pair corpus.
    /// - witness: `template::tests::drafts_equal_fresh_runs_across_the_edit_traces`
    #[spec(ensures: |output| matches!(output, Maybe::Absent(Unheld::Unseen))
        == self.slots.iter().all(|slot| slot.key != *family.key()))]
    #[inline]
    pub fn template(
        &self,
        family: &Family,
    ) -> Maybe<&Template, Unheld>
    {
        match self.slots.iter().find(|slot| slot.key == *family.key()) {
            | Some(&Slot {
                held: Held::Template(ref template),
                ..
            }) => Maybe::Present(template),
            | Some(_) => Maybe::Absent(Unheld::Vacated),
            | None => Maybe::Absent(Unheld::Unseen),
        }
    }

    /// Hold a template for a family's key, as if the key's last family had
    /// emitted it: one seeded from a stored run, say.
    ///
    /// # Specification
    /// - ensures: the next draft of a family with this key starts from
    ///   `template`; the key's controller state is kept. Holding confers no
    ///   authority: the kernel judges every draft from it.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a held template whose join is corrupted is refused by
    ///   the kernel, and its family falls to the producer.
    /// - witness: `template::tests::a_kernel_refused_draft_falls_back_to_the_producer`
    #[spec(ensures: |()| matches!(self.template(family), Maybe::Present(_)))]
    #[inline]
    pub fn hold(
        &mut self,
        family: &Family,
        template: Template,
    )
    {
        match self.slots.iter_mut().find(|slot| slot.key == *family.key()) {
            | Some(slot) => slot.held = Held::Template(template),
            | None => self.slots.push(Slot {
                key: family.key().clone(),
                held: Held::Template(template),
                controls: Controls::fresh(),
            }),
        }
    }

    /// Admit one family: from a draft of the memo's template when the
    /// controller drafts and the kernel admits the draft whole, from the
    /// producer otherwise.
    ///
    /// # Specification
    /// - ensures: an `Admitted` family's every member was admitted by the
    ///   kernel under the reported schema. A drafted one's schema is the one a
    ///   fresh run of the producer would propose for the same members: its
    ///   skeleton and arms pass the departure checks, its arms are numbered by
    ///   first selection, and its proposal is emitted canonically. The producer
    ///   did not run for it, and under the memoized price no kernel replay
    ///   spent more than the producer's per-check allowance. A draft the kernel
    ///   refuses is never reported as admitted: its family goes to the
    ///   producer. `Partial` follows only the kernel's work-bound refusal of
    ///   the producer's schema, from the template held before this family. The
    ///   held template becomes the admitted one, is vacated by a plain family,
    ///   and is otherwise kept.
    /// - fails: caller-budget exhaustion; a lookup or syntax error from
    ///   analysis, drafting or emission.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `StageError::Exhausted` or the propagated `StageError`.
    ///
    /// # Adequacy
    /// - hypothesis: L2/L3 — every drafted schema across the edit-pair corpus
    ///   is compared with a fresh run's byte for byte; a draft whose template
    ///   is corrupted so the kernel refuses it falls back to the producer; a
    ///   work-bound family admits its template subfamily; a scripted clock
    ///   drives the controller.
    /// - witness: `template::tests::drafts_equal_fresh_runs_across_the_edit_traces`
    /// - witness: `template::tests::a_kernel_refused_draft_falls_back_to_the_producer`
    /// - witness: `template::tests::a_work_bound_family_admits_its_template_subfamily`
    /// - witness: `template::memo::tests::the_fresh_arm_cap_withdraws_a_widening_that_costs_the_producers_time`
    #[spec(captures: [available = budget.0], ensures: |output| budget.0 <= available
        && output.as_ref().ok().is_none_or(|report| match report.admission {
            FamilyAdmission::Admitted { origin: Origin::Drafted(kind), .. } =>
                report.drafting == Drafting::Accepted(kind) && report.spent.producing.is_zero(),
            FamilyAdmission::Partial { ref members, .. } =>
                !members.is_empty() && members.len() <= family.members.len(),
            _ => !matches!(report.drafting, Drafting::Accepted(_)),
        }))]
    #[inline]
    pub fn admit_family<C>(
        &mut self,
        arena: &Arena,
        family: &Family,
        gate: PriceGate,
        cache: &mut InheritanceCache,
        budget: &mut Budget,
        clock: &mut C,
    ) -> Result<FamilyReport, StageError>
    where
        C: Clock,
    {
        let members = family.members.as_slice();
        let index = match self.slots.iter().position(|slot| slot.key == *family.key()) {
            | Some(index) => index,
            | None => {
                self.slots.push(Slot {
                    key: family.key().clone(),
                    held: Held::Vacant,
                    controls: Controls::fresh(),
                });
                self.slots.len().saturating_sub(1)
            },
        };
        let Self {
            ref mut slots,
            ref mut switch,
            ref mut drafter,
            ref mut row,
        } = *self;
        let slot = slots.get_mut(index).ok_or(StageError::Unbalanced)?;
        let mut spent = Spent::default();
        let mut drafting = Drafting::Unmemoized;
        if let Held::Template(ref memo) = slot.held {
            match slot.controls.decide(switch) {
                | Decision::Decline(decline) => drafting = Drafting::Declined(decline),
                | Decision::Draft => {
                    let begun = clock.now();
                    let mut cap = Cap {
                        producing: slot.controls.producing,
                        arm: switch.arm,
                    };
                    let attempt = memo.attempt(arena, members, gate, &mut cap, drafter, clock)?;
                    switch.arm = cap.arm;
                    spent.drafting = since(clock, begun);
                    drafting = match attempt {
                        | Attempt::Withdrawn(withdrawn) => withdrawn,
                        | Attempt::Ready(draft, kind) => {
                            let begun = clock.now();
                            let choices = rows(
                                &draft.choices,
                                PointCount(memo.entries.len()),
                                MemberCount::from(members.len()),
                            )?;
                            let judged =
                                judge(arena, members, draft.proposal, &choices, row, budget)?;
                            spent.admitting = since(clock, begun);
                            let allowance = usize::from(draft.cost.template_size);
                            match judged {
                                | Judged::Refused(refusal) => Drafting::Refused(refusal),
                                | Judged::Admitted(schema)
                                    if gate == PriceGate::Memoized
                                        && schema.largest_replay().0 > allowance =>
                                {
                                    Drafting::ReplayBound(schema.largest_replay())
                                },
                                | Judged::Admitted(schema) => {
                                    slot.controls.record(
                                        switch,
                                        Acceptance::Accepted,
                                        spent.drafting,
                                    );
                                    if let Held::Template(ref mut held) = slot.held {
                                        draft.revision.apply(held, draft.cost);
                                    }
                                    return Ok(FamilyReport {
                                        admission: FamilyAdmission::Admitted {
                                            schema,
                                            origin: Origin::Drafted(kind),
                                        },
                                        drafting: Drafting::Accepted(kind),
                                        spent,
                                    });
                                },
                            }
                        },
                    };
                    slot.controls
                        .record(switch, Acceptance::Refused, spent.drafting);
                },
            }
        }
        let begun = clock.now();
        let analysis = analyze(arena, members)?;
        let candidate = match analysis {
            | Analysis::Candidate(candidate) => candidate,
            | Analysis::Refused { reason, .. } => {
                spent.producing = since(clock, begun);
                slot.controls.producing = Estimate::Measured(spent.producing);
                slot.held = Held::Vacant;
                return Ok(FamilyReport {
                    admission: FamilyAdmission::Plain(reason),
                    drafting,
                    spent,
                });
            },
        };
        let prices = candidate.prices();
        let pays = match gate {
            | PriceGate::Unmemoized => prices.unmemoized.is_ok(),
            | PriceGate::Memoized => prices.memoized.is_ok(),
        };
        if !pays {
            let cost = candidate.cost();
            spent.producing = since(clock, begun);
            slot.controls.producing = Estimate::Measured(spent.producing);
            slot.held = Held::Vacant;
            return Ok(FamilyReport {
                admission: FamilyAdmission::Plain(TemplateRefusal::DoesNotPay {
                    template_size: cost.template_size,
                    plain_size: cost.plain_size,
                }),
                drafting,
                spent,
            });
        }
        let admission = candidate.admission_candidate()?;
        let production = candidate.produce(gate, cache, budget)?;
        spent.producing = since(clock, begun);
        slot.controls.producing = Estimate::Measured(spent.producing);
        let refusal = match production {
            | Production::Go(template) => {
                let begun = clock.now();
                let choices: Vec<&[Choice]> = admission.rows.iter().map(Vec::as_slice).collect();
                let judged = judge(arena, members, admission.proposal, &choices, row, budget)?;
                spent.admitting = spent.admitting.saturating_add(since(clock, begun));
                match judged {
                    | Judged::Admitted(schema) => {
                        let begun = clock.now();
                        let held = template.compacted()?;
                        spent.drafting = spent.drafting.saturating_add(since(clock, begun));
                        slot.held = Held::Template(held);
                        return Ok(FamilyReport {
                            admission: FamilyAdmission::Admitted {
                                schema,
                                origin: Origin::Produced,
                            },
                            drafting,
                            spent,
                        });
                    },
                    | Judged::Refused(refusal) => refusal,
                }
            },
            | Production::SchemaWorkBound { .. } => Refusal::SchemaWorkBound,
            | Production::Plain { reason, .. } => {
                slot.held = Held::Vacant;
                return Ok(FamilyReport {
                    admission: FamilyAdmission::Plain(reason),
                    drafting,
                    spent,
                });
            },
            | Production::WorkBoundExceeded { bound, .. } => {
                return Ok(FamilyReport {
                    admission: FamilyAdmission::WorkBoundExceeded(bound),
                    drafting,
                    spent,
                });
            },
        };
        let refused = FamilyReport {
            admission: FamilyAdmission::Refused(refusal),
            drafting,
            spent,
        };
        if refusal != Refusal::SchemaWorkBound {
            return Ok(refused);
        }
        let Held::Template(ref old) = slot.held
        else {
            return Ok(refused);
        };
        let begun = clock.now();
        let matched = old.walk_partial(arena, members, drafter)?;
        let finished = if matched.is_empty() {
            Finished::Unfit(Unfit::DoesNotPay(TemplateRefusal::EmptyFamily))
        }
        else {
            old.finish(
                arena,
                members,
                Coverage::Partial(&matched),
                drafter,
                gate,
                clock,
            )?
        };
        spent.drafting = spent.drafting.saturating_add(since(clock, begun));
        let Finished::Ready(draft) = finished
        else {
            return Ok(FamilyReport { spent, ..refused });
        };
        let begun = clock.now();
        let subfamily: Vec<Step> = matched
            .iter()
            .filter_map(|member| members.get(usize::from(*member)).copied())
            .collect();
        let choices = rows(
            &draft.choices,
            PointCount(old.entries.len()),
            MemberCount::from(subfamily.len()),
        )?;
        let judged = judge(arena, &subfamily, draft.proposal, &choices, row, budget)?;
        spent.admitting = spent.admitting.saturating_add(since(clock, begun));
        let Judged::Admitted(schema) = judged
        else {
            return Ok(FamilyReport { spent, ..refused });
        };
        Ok(FamilyReport {
            admission: FamilyAdmission::Partial {
                schema,
                members: matched,
            },
            drafting,
            spent,
        })
    }
}
