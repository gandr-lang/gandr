//! The machines a run holds: each one the dovetailing scheduler of
//! `theory-exact-reals` on the two poles of an open root.
//!
//! `decide` mints a machine over a plan whose root is an open proposition,
//! such as `a < b`. The machine has two obligations: that the root holds, and
//! that it fails. A quantum is one certificate step, and the poles take their
//! quanta in turn. A machine decides when one pole certifies. The checker
//! replays that certificate once, and the verdict stays. Every other end of a
//! run is a named stop: the run spends its budget, or both poles suspend. No
//! stop reads as false.
//!
//! The checkpoint of a machine is the one form that leaves the run. Its text
//! is the lowercase hexadecimal of three parts: the byte length of the plan,
//! four bytes with the least significant first; the canonical bytes of the
//! plan; and the canonical bytes of the checkpoint of the scheduler. `restore`
//! validates the plan again and replays the steps again, so the integrity of
//! the text never stands in for its validity.

use alloc::rc::Rc;
use alloc::vec::Vec;
use core::fmt;
use core::num::NonZeroU32;

use gandr_theory_exact_reals::Answer;
use gandr_theory_exact_reals::Budget;
use gandr_theory_exact_reals::CheckerQuotas;
use gandr_theory_exact_reals::Demand;
use gandr_theory_exact_reals::Dovetail;
use gandr_theory_exact_reals::EncodedCheckpoint;
use gandr_theory_exact_reals::EncodedPlan;
use gandr_theory_exact_reals::Obligation;
use gandr_theory_exact_reals::Outcome;
use gandr_theory_exact_reals::Position;
use gandr_theory_exact_reals::Quantum;
use gandr_theory_exact_reals::Rounds;
use gandr_theory_exact_reals::Stop;
use gandr_theory_exact_reals::ValidatedPlan;
use gandr_theory_exact_reals::check;
use gandr_theory_exact_reals::validate;

use super::Counters;
use super::Declined;
use super::Decoded;
use super::Limits;
use super::MachineHandle;
use super::Quanta;
use super::evidence;

/// What a machine knows of its root after its last quantum.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) enum Verdict
{
    /// The root holds, by a certificate that the checker replays.
    Holds,
    /// The root fails, by a certificate that the checker replays.
    Fails,
    /// No quantum runs yet: a resumed machine before its first step.
    Pending,
    /// The last run spends its budget with a pole live.
    Exhausted,
    /// The last run stops at a cancellation with a pole live.
    Cancelled,
    /// Both poles suspend: the machine cannot go on with either.
    Suspended,
}

impl fmt::Display for Verdict
{
    /// Write the name of the verdict, as a program reads it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            Self::Holds => "holds",
            Self::Fails => "fails",
            Self::Pending => "pending",
            Self::Exhausted => "exhausted",
            Self::Cancelled => "cancelled",
            Self::Suspended => "suspended",
        })
    }
}

/// One machine: its plan, its scheduler, its poles and what it knows.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Machine
{
    /// The plan that the machine decides.
    plan: Rc<ValidatedPlan>,
    /// The scheduler on the poles.
    dovetail: Dovetail<Rc<ValidatedPlan>>,
    /// The obligation at each position of the scheduler.
    poles: Vec<Obligation>,
    /// The verdict after the last quantum.
    verdict: Verdict,
    /// The obligations that are live after the last quantum.
    live: usize,
    /// The steps of the certificate that decides the machine, or zero.
    certificate: usize,
    /// The quotas of the checker that replays each certificate of the machine.
    quotas: CheckerQuotas,
    /// The certificate steps that the checker replays for the machine.
    replayed: usize,
    /// The checkpoints that the machine spells.
    checkpoints: usize,
    /// The runs of the machine that stop at a cancellation.
    cancellations: u64,
}

/// The machines that a run holds, each at the place that its handle names.
///
/// The table is empty until the first `decide` or `restore`, so a run that
/// decides nothing allocates nothing for it.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(super) struct Machines
{
    /// The machines, in the order that the run mints them.
    held: Vec<Machine>,
}

impl Machines
{
    /// Mint a machine over `plan` on the two poles of its root, and run it for
    /// `budget` quanta under the quotas of `limits`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the verdict after the run and the handle of the machine, the
    ///   place where the table now holds it. The verdict is `holds` or `fails`
    ///   only with a certificate that the checker replays to that pole.
    /// - fails: a full table, a root that is no open proposition, and a
    ///   certificate that the checker refuses or that concludes another
    ///   judgement, each with the table unchanged.
    /// - panics: none.
    /// - executable: none — the clause speaks of the machine's certificate and
    ///   its replay, which the function makes.
    ///
    /// # Errors
    /// [`Declined::Machines`], [`Declined::Real`], [`Declined::Replay`] or
    /// [`Declined::Mismatch`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `sqrt 2 < 3/2` holds; `sqrt 2 · sqrt 2 < 2` spends
    ///   the smaller budgets and suspends at the checker's quota, and `sqrt 2 <
    ///   sqrt 2` spends each budget, neither read as false.
    /// - witness: `tests::run::a_script_decides_comparisons_through_reals_5703`
    pub(super) fn decide(
        &mut self,
        plan: Rc<ValidatedPlan>,
        budget: Quanta,
        limits: &Limits,
    ) -> Result<(Verdict, MachineHandle), Declined>
    {
        if self.held.len() >= limits.machines {
            return Err(Declined::Machines(limits.machines));
        }
        let root = plan.plan().root().node();
        let (Ok(holds), Ok(fails)) = (
            Obligation::new(&plan, root, Demand::Holds),
            Obligation::new(&plan, root, Demand::Fails),
        )
        else {
            return Err(Declined::Real);
        };
        let dovetail = Dovetail::new(
            Rc::clone(&plan),
            [holds, fails],
            Quantum::from(NonZeroU32::MIN),
            limits.checker,
        );
        let mut machine = Machine {
            plan,
            dovetail,
            poles: alloc::vec![holds, fails],
            verdict: Verdict::Pending,
            live: 2,
            certificate: 0,
            quotas: limits.checker,
            replayed: 0,
            checkpoints: 0,
            cancellations: 0,
        };
        machine.advance(budget)?;
        let handle = MachineHandle(self.held.len());
        let verdict = machine.verdict;
        self.held.push(machine);
        Ok((verdict, handle))
    }

    /// Run the machine at `handle` for one more quantum.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the verdict after the quantum and the same handle. A decided
    ///   machine runs no quantum, and its verdict stays.
    /// - fails: a handle that names no machine, and a certificate that the
    ///   checker refuses or that concludes another judgement.
    /// - panics: none.
    /// - executable: none — as [`Self::decide`].
    ///
    /// # Errors
    /// [`Declined::NoMachine`], [`Declined::Replay`] or
    /// [`Declined::Mismatch`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the resumed machine of the exemplar steps to the
    ///   verdict of an uninterrupted run.
    /// - witness: `tests::run::a_script_decides_comparisons_through_reals_5703`
    pub(super) fn step(
        &mut self,
        handle: MachineHandle,
    ) -> Result<(Verdict, MachineHandle), Declined>
    {
        let machine = self.held.get_mut(handle.0).ok_or(Declined::NoMachine)?;
        machine.advance(Quanta(1))?;
        Ok((machine.verdict, handle))
    }

    /// The checkpoint of the machine at `handle`, with its plan, as the bytes
    /// that its text spells.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the length of the plan as four bytes with the least
    ///   significant first, the canonical bytes of the plan, and then the
    ///   canonical bytes of the checkpoint of the scheduler. The machine counts
    ///   one more checkpoint.
    /// - fails: a handle that names no machine, a machine that is decided or
    ///   holds no live obligation, and a plan too long for its length.
    /// - panics: none.
    /// - executable: none — the clause speaks of the scheduler's canonical
    ///   bytes, which the scheduler writes.
    ///
    /// # Errors
    /// [`Declined::NoMachine`], [`Declined::Settled`] or
    /// [`Declined::Framing`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the exemplar's checkpoint after one quantum resumes
    ///   to the outcome of an uninterrupted run.
    /// - witness: `tests::run::a_script_decides_comparisons_through_reals_5703`
    pub(super) fn checkpoint(
        &mut self,
        handle: MachineHandle,
    ) -> Result<Decoded, Declined>
    {
        let machine = self.held.get_mut(handle.0).ok_or(Declined::NoMachine)?;
        if machine.live == 0 || matches!(machine.verdict, Verdict::Holds | Verdict::Fails) {
            return Err(Declined::Settled);
        }
        let plan: Vec<u8> = machine.plan.plan().encode().into();
        let length = u32::try_from(plan.len()).ok().ok_or(Declined::Framing)?;
        let checkpoint = machine.dovetail.checkpoint();
        let mut bytes = Vec::new();
        bytes.extend_from_slice(&length.to_le_bytes());
        bytes.extend_from_slice(&plan);
        bytes.extend_from_slice(checkpoint.as_ref());
        machine.checkpoints = machine.checkpoints.saturating_add(1);
        Ok(Decoded(bytes))
    }

    /// Mint a machine from the checkpoint that `bytes` hold, under the quotas
    /// of `limits`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the handle of a machine whose plan passes validation again
    ///   and whose steps replay again, each obligation a pole of the root of
    ///   that plan. Its next quanta do what the machine that wrote the
    ///   checkpoint would do. The checker steps of the machine count the steps
    ///   that the restore replays.
    /// - fails: a full table, bytes that frame no plan, a plan that the
    ///   validation pass refuses, a checkpoint that the scheduler refuses, and
    ///   an obligation that is no pole of the root, each with the table
    ///   unchanged and the check named.
    /// - panics: none.
    /// - executable: none — the clause speaks of the resumed scheduler's runs.
    ///
    /// # Errors
    /// [`Declined::Machines`], [`Declined::Framing`], [`Declined::Refused`],
    /// [`Declined::Resumed`] or [`Declined::Foreign`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the exemplar's checkpoint resumes; a checkpoint with
    ///   a byte changed is refused by name.
    /// - witness: `tests::run::a_script_decides_comparisons_through_reals_5703`
    pub(super) fn restore(
        &mut self,
        bytes: &Decoded,
        limits: &Limits,
    ) -> Result<MachineHandle, Declined>
    {
        if self.held.len() >= limits.machines {
            return Err(Declined::Machines(limits.machines));
        }
        let (&length, rest) = bytes.0.split_first_chunk::<4>().ok_or(Declined::Framing)?;
        let length = usize::try_from(u32::from_le_bytes(length))
            .ok()
            .ok_or(Declined::Framing)?;
        let (plan, checkpoint) = rest.split_at_checked(length).ok_or(Declined::Framing)?;
        let plan = Rc::new(
            validate(EncodedPlan::from(plan), &limits.plan, &evidence())
                .map_err(Declined::Refused)?,
        );
        let dovetail = Dovetail::resume(Rc::clone(&plan), EncodedCheckpoint::from(checkpoint))
            .map_err(Declined::Resumed)?;
        let root = plan.plan().root().node();
        let poles: Vec<Obligation> = (0_usize ..)
            .map_while(|position| dovetail.obligation(Position::from(position)))
            .collect();
        let foreign = poles.iter().any(|pole| {
            pole.node() != root || !matches!(pole.demand(), Demand::Holds | Demand::Fails)
        });
        if poles.is_empty() || foreign {
            return Err(Declined::Foreign);
        }
        let replayed = (0 .. poles.len())
            .filter_map(|position| dovetail.written(Position::from(position)))
            .fold(0_usize, |total, steps| {
                total.saturating_add(usize::from(steps))
            });
        let handle = MachineHandle(self.held.len());
        self.held.push(Machine {
            plan,
            dovetail,
            live: poles.len(),
            poles,
            verdict: Verdict::Pending,
            certificate: 0,
            quotas: limits.checker,
            replayed,
            checkpoints: 0,
            cancellations: 0,
        });
        Ok(handle)
    }

    /// The work counters of the machine at `handle`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the quanta that the machine spends over all its runs, the
    ///   obligations that it holds, and the steps of the certificate that
    ///   decides it, or zero. Then the obligations live after its last quantum,
    ///   no cache hits, the most pieces that a search of it holds at once, the
    ///   checker steps, the checkpoints and the cancellations.
    /// - fails: a handle that names no machine.
    /// - panics: none.
    /// - executable: none — the clause restates the counters of the machine.
    ///
    /// # Errors
    /// [`Declined::NoMachine`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the exemplar's resumed machine reports the work of
    ///   the uninterrupted one, and the exemplars report each counter.
    /// - witness: `tests::run::a_script_decides_comparisons_through_reals_5703`
    pub(super) fn report(
        &self,
        handle: MachineHandle,
    ) -> Result<Counters, Declined>
    {
        let machine = self.held.get(handle.0).ok_or(Declined::NoMachine)?;
        let positions = || (0 .. machine.poles.len()).map(Position::from);
        let quanta = positions()
            .filter_map(|position| machine.dovetail.spent(position))
            .fold(0_u64, |total, spent| total.saturating_add(u64::from(spent)));
        let regions = positions()
            .filter_map(|position| machine.dovetail.regions(position))
            .map(usize::from)
            .max()
            .unwrap_or(0);
        Ok(Counters {
            quanta,
            obligations: machine.poles.len(),
            certificate: machine.certificate,
            frontier: machine.live,
            hits: 0,
            regions,
            replayed: machine.replayed,
            checkpoints: machine.checkpoints,
            cancellations: machine.cancellations,
        })
    }
}

impl Machine
{
    /// Run the scheduler for `budget` quanta and read what it knows of the
    /// root.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a decided machine runs nothing. Otherwise the verdict is the
    ///   pole that certifies, once the checker replays its certificate to that
    ///   pole; else the stop of the run with a pole live; else `suspended`. A
    ///   run that stops at a cancellation counts one, and each replay adds its
    ///   steps to the checker steps.
    /// - fails: a certificate that the checker refuses, or one that concludes
    ///   another judgement than its pole.
    /// - panics: none.
    /// - executable: none — as [`Machines::decide`].
    ///
    /// # Errors
    /// [`Declined::Replay`] or [`Declined::Mismatch`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Machines::decide`].
    /// - witness: `tests::run::a_script_decides_comparisons_through_reals_5703`
    fn advance(
        &mut self,
        budget: Quanta,
    ) -> Result<(), Declined>
    {
        if matches!(self.verdict, Verdict::Holds | Verdict::Fails) {
            return Ok(());
        }
        let quotas = self.quotas;
        let report = self
            .dovetail
            .run(Budget::from(budget.0), Rounds::from(u64::MAX), || false);
        if matches!(report.stop(), Stop::Cancelled) {
            self.cancellations = self.cancellations.saturating_add(1);
        }
        let mut decided = None;
        let mut replayed = 0_usize;
        let mut live = 0_usize;
        let mut stopped = Verdict::Suspended;
        for (position, pole) in self.poles.iter().enumerate() {
            match report.outcome(Position::from(position)) {
                Some(Outcome::Certified(certificate)) => {
                    let checked =
                        check(&self.plan, certificate, &quotas).map_err(Declined::Replay)?;
                    match pole.answered_by(checked.conclusion()) {
                        Answer::Answers => {},
                        Answer::Misses => return Err(Declined::Mismatch),
                    }
                    let verdict = match pole.demand() {
                        Demand::Holds => Verdict::Holds,
                        Demand::Fails => Verdict::Fails,
                        Demand::Encloses { .. } => return Err(Declined::Mismatch),
                    };
                    let steps = usize::from(certificate.step_count());
                    replayed = replayed.saturating_add(steps);
                    decided = Some((verdict, steps));
                },
                Some(Outcome::Pending) => {
                    live = live.saturating_add(1);
                    stopped = Verdict::Pending;
                },
                Some(Outcome::Exhausted) => {
                    live = live.saturating_add(1);
                    stopped = Verdict::Exhausted;
                },
                Some(Outcome::Cancelled) => {
                    live = live.saturating_add(1);
                    stopped = Verdict::Cancelled;
                },
                Some(Outcome::Suspended(_)) | None => {},
            }
        }
        self.live = live;
        self.replayed = self.replayed.saturating_add(replayed);
        match decided {
            Some((verdict, steps)) => {
                self.verdict = verdict;
                self.certificate = steps;
            },
            None => self.verdict = stopped,
        }
        Ok(())
    }
}
