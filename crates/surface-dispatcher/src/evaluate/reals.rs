//! The exact reals a run reaches: where the operations of `Reals` go.
//!
//! The host at a program's entry holds the run's [`Reals`]: the plans of
//! `theory-exact-reals` that the validation pass admits, and the machines that
//! decide their open roots. `admit` reads its string as the canonical bytes of
//! a plan in lowercase hexadecimal. It validates them under the default
//! quotas, against the evidence of stages A and C, and replies the place of
//! the plan in the table. So a plan is an integer that names a plan this host
//! holds, and it never crosses. `enclose` takes a plan and a precision `k`. It
//! runs the refinement machine on the root of the plan until the machine
//! certifies an enclosure no wider than `2^-k`. The checker replays the
//! certificate, and the host replies the two ends, each spelled
//! `<mantissa>p<exponent>` for `mantissa · 2^exponent`.
//!
//! `decide`, `step`, `checkpoint`, `restore` and `report` work on the machines
//! that [`machine`] holds. A machine decides an open root such as `a < b`
//! within a budget of quanta, and only a certificate that the checker replays
//! makes it hold or fail. Each other end of a run is a named stop.
//!
//! An operation that fails is declined, and the run is stuck at it. Before
//! the decline, the host writes one line to standard error. The line names
//! the operation and the cause: the site and the check of a refused plan or
//! checkpoint, or the other cause of the decline.
//!
//! # References
//!
//! - `vault:01a178aa-a419-7ab1-82e7-40a4f95938c6` — anchor: the first adapter
//!   of the decision register, a handle that names a plan the host holds, and §
//!   The architecture, where the host validates each value that crosses.
//! - `vault:01a1aa2d-a69c-7030-91e0-337d68d88151` — anchor: §
//!   presented-spaces-crates puts the host adapter of stage C in the
//!   dispatcher.

use alloc::boxed::Box;
use alloc::format;
use alloc::rc::Rc;
use alloc::string::String;
use alloc::string::ToString as _;
use alloc::vec::Vec;
use core::fmt;
use core::num::NonZeroU32;

use anodized::spec;
use gandr_core_sequent::ConstructorTag;
use gandr_core_sequent::HeapValue;
use gandr_core_sequent::HeapValueId;
use gandr_core_sequent::ProducerArity;
use gandr_core_term::effect::OperationName;
use gandr_core_term::effect::host::REALS;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Sign;
use gandr_kernel_term::StringLiteral;
use gandr_runtime_emitter::HostReply;
use gandr_runtime_emitter::HostRequest;
use gandr_runtime_emitter::HostValues;
use gandr_theory_exact_reals::Answer;
use gandr_theory_exact_reals::Budget;
use gandr_theory_exact_reals::CertificateRefusal;
use gandr_theory_exact_reals::CheckerQuotas;
use gandr_theory_exact_reals::Conclusion;
use gandr_theory_exact_reals::Demand;
use gandr_theory_exact_reals::Dovetail;
use gandr_theory_exact_reals::Dyadic;
use gandr_theory_exact_reals::EncodedPlan;
use gandr_theory_exact_reals::Endpoint;
use gandr_theory_exact_reals::Evidence;
use gandr_theory_exact_reals::EvidenceTable;
use gandr_theory_exact_reals::Exponent;
use gandr_theory_exact_reals::Judgement;
use gandr_theory_exact_reals::Obligation;
use gandr_theory_exact_reals::Outcome;
use gandr_theory_exact_reals::Position;
use gandr_theory_exact_reals::Quantum;
use gandr_theory_exact_reals::Quotas;
use gandr_theory_exact_reals::Refusal;
use gandr_theory_exact_reals::ResumeError;
use gandr_theory_exact_reals::Rounds;
use gandr_theory_exact_reals::SuspendReason;
use gandr_theory_exact_reals::ValidatedPlan;
use gandr_theory_exact_reals::check;
use gandr_theory_exact_reals::validate;

use self::machine::MACHINES;
use self::machine::Machines;
use self::machine::QUANTA;
use self::machine::Verdict;
use super::Console;
use super::Printed;
use super::console::Line;

mod machine;

/// The operation of [`REALS`] that validates a plan.
const ADMIT: &str = "admit";
/// The operation of [`REALS`] that encloses the root of a plan.
const ENCLOSE: &str = "enclose";
/// The operation of [`REALS`] that mints a machine on an open root.
const DECIDE: &str = "decide";
/// The operation of [`REALS`] that runs one more quantum of a machine.
const STEP: &str = "step";
/// The operation of [`REALS`] that spells the checkpoint of a machine.
const CHECKPOINT: &str = "checkpoint";
/// The operation of [`REALS`] that mints a machine from a checkpoint.
const RESTORE: &str = "restore";
/// The operation of [`REALS`] that gives the work counters of a machine.
const REPORT: &str = "report";

/// The most plans that one run holds.
const PLANS: usize = 64;

/// The finest precision that `enclose` takes: an enclosure no wider than
/// `2^-4096`.
const PRECISION: i32 = 1 << 12;

/// The most certificate steps that one `enclose` does: the step quota of the
/// checker.
const STEPS: u64 = 1 << 16;

/// The plans and the machines that a run holds, each at the place that its
/// handle names.
///
/// The tables are empty until the first `admit`, so a run that performs no
/// `Reals` operation allocates nothing for them.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(super) struct Reals
{
    /// The validated plans, in the order of their `admit`. A machine shares
    /// the plan that it decides.
    plans: Vec<Rc<ValidatedPlan>>,
    /// The machines, in the order that the run mints them.
    machines: Machines,
}

/// The handle of a plan: its place in the table of the run.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Handle(usize);

/// The bytes that the hexadecimal text of an `admit` spells.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
struct Decoded(Vec<u8>);

/// The handle of a machine: its place in the table of the run.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct MachineHandle(usize);

/// A budget of quanta, from zero to [`QUANTA`].
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Quanta(u64);

/// The work counters of a machine, in the order that `report` replies them.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct Counters
{
    /// The quanta that the machine spends over all its runs, before a
    /// checkpoint too.
    quanta: u64,
    /// The obligations that the machine holds: both poles for a minted
    /// machine, and the poles live at its checkpoint for a restored one.
    obligations: usize,
    /// The steps of the certificate that decides the machine, or zero.
    certificate: usize,
}

/// What the payload of a `Reals` operation asks, read out of the store of the
/// run.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Asked<'values>
{
    /// Validate the plan that the text spells.
    Admit(&'values StringLiteral),
    /// Enclose the root of the plan at the handle no wider than `2^width`.
    Enclose
    {
        /// The place of the plan in the table.
        handle: Handle,
        /// The power of two that bounds the width, from `-PRECISION` to zero.
        width: Exponent,
    },
    /// Mint a machine on the open root of the plan at the handle, and run it
    /// for a budget of quanta.
    Decide
    {
        /// The place of the plan in the table.
        handle: Handle,
        /// The quanta of the first run.
        budget: Quanta,
    },
    /// Run one more quantum of the machine at the handle.
    Step(MachineHandle),
    /// Spell the checkpoint of the machine at the handle.
    Checkpoint(MachineHandle),
    /// Mint a machine from the checkpoint that the text spells.
    Restore(&'values StringLiteral),
    /// Give the work counters of the machine at the handle.
    Report(MachineHandle),
}

/// What a `Reals` operation answers, to be allocated as its reply.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Answered
{
    /// The handle of a plan that the table now holds.
    Plan(Handle),
    /// The lower end and the upper end of an enclosure, each spelled.
    Enclosure(String, String),
    /// The verdict of a machine, and its handle.
    Verdict(Verdict, MachineHandle),
    /// The lowercase hexadecimal of a checkpoint.
    Text(String),
    /// The handle of a machine that the table now holds.
    Machine(MachineHandle),
    /// The work counters of a machine.
    Counters(Counters),
}

/// Why a run of the machine stops short of an enclosure.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Stopped
{
    /// The run stops at its limit of rounds with the obligation live.
    Pending,
    /// The run spends its budget of steps.
    Exhausted,
    /// The run stops at a cancellation.
    Cancelled,
    /// The machine cannot go on, for the stated reason.
    Suspended(SuspendReason),
}

/// Why the host declines a `Reals` operation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Declined
{
    /// The payload is not what `Reals` declares.
    Payload,
    /// The text is not the lowercase hexadecimal of a byte string.
    Hexadecimal,
    /// The run holds [`PLANS`] plans already.
    Full,
    /// The validation pass refuses the plan.
    Refused(Refusal),
    /// The run holds no plan at the handle.
    Unknown,
    /// The precision is below zero or past [`PRECISION`].
    Precision,
    /// The root of the plan is no real.
    Proposition,
    /// The machine stops short of an enclosure.
    Unsettled(Stopped),
    /// The checker refuses the certificate.
    Replay(CertificateRefusal),
    /// The certificate concludes another judgement than the enclosure asked.
    Mismatch,
    /// The root of the plan is no open proposition.
    Real,
    /// The budget is past [`QUANTA`].
    Quanta,
    /// The run holds [`MACHINES`] machines already.
    Machines,
    /// The run holds no machine at the handle.
    NoMachine,
    /// The machine is decided or holds no live obligation.
    Settled,
    /// The bytes do not frame a plan of the length that they state.
    Framing,
    /// The scheduler refuses the checkpoint, at the check named.
    Resumed(ResumeError),
    /// The checkpoint asks another obligation than a pole of the root.
    Foreign,
    /// The store refuses the reply.
    Store,
}

impl fmt::Display for Declined
{
    /// Write the cause as one line.
    ///
    /// # Specification
    /// - ensures: writes one phrase per variant, no two alike, with the refusal
    ///   of the validation pass or of the checker after its phrase.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Errors
    /// Propagates the formatter's write failure.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — text that is not hexadecimal, a forged plan, an
    ///   unknown handle and a precision past the quota, each named on standard
    ///   error; a budget past the quota, an unknown machine and a corrupt
    ///   checkpoint, each named too.
    /// - witness: `tests::run::a_script_encloses_the_square_root_of_two_5700`
    /// - witness: `tests::run::a_script_decides_comparisons_through_reals_5703`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Payload => f.write_str("the payload is not what `Reals` declares"),
            Self::Hexadecimal => {
                f.write_str("the text is not the lowercase hexadecimal of a byte string")
            },
            Self::Full => write!(f, "the run holds {PLANS} plans already"),
            Self::Refused(refusal) => write!(f, "the plan is refused at {refusal}"),
            Self::Unknown => f.write_str("the run holds no plan at the handle"),
            Self::Precision => write!(f, "the precision is not from 0 to {PRECISION}"),
            Self::Proposition => f.write_str("the root of the plan is no real"),
            Self::Unsettled(stopped) => {
                f.write_str("the machine stops short of an enclosure: ")?;
                f.write_str(match stopped {
                    Stopped::Pending => "the run is pending",
                    Stopped::Exhausted => "the run spends its budget of steps",
                    Stopped::Cancelled => "the run is cancelled",
                    Stopped::Suspended(SuspendReason::NoRule) => {
                        "the certificate format has no rule for the form of the root"
                    },
                    Stopped::Suspended(SuspendReason::Quota) => {
                        "the next step puts the certificate past the quotas of the checker"
                    },
                    Stopped::Suspended(SuspendReason::Opposed) => "a step concludes the other pole",
                })
            },
            Self::Replay(refusal) => write!(f, "the certificate does not replay: {refusal}"),
            Self::Mismatch => {
                f.write_str("the certificate concludes another judgement than the enclosure asked")
            },
            Self::Real => f.write_str("the root of the plan is no open proposition"),
            Self::Quanta => write!(f, "the budget is not from 0 to {QUANTA} quanta"),
            Self::Machines => write!(f, "the run holds {MACHINES} machines already"),
            Self::NoMachine => f.write_str("the run holds no machine at the handle"),
            Self::Settled => f.write_str(
                "the machine is decided or holds no live obligation, so no checkpoint resumes it",
            ),
            Self::Framing => {
                f.write_str("the checkpoint does not frame a plan of its stated length")
            },
            Self::Resumed(error) => write!(f, "the checkpoint is refused: {error}"),
            Self::Foreign => {
                f.write_str("the checkpoint asks another obligation than a pole of the root")
            },
            Self::Store => f.write_str("the store refuses the reply"),
        }
    }
}

/// Serve the `Reals` operation that `request` offers on `reals`: the reply
/// that the host gives, or nothing when the request is another interface's.
///
/// # Specification
/// - requires: nothing.
/// - ensures: for `admit`, the plan that the hexadecimal text spells, validated
///   and held, and its handle as the reply; for `enclose`, the two ends of a
///   certified enclosure of the root no wider than `2^-k`, which the checker
///   replays before the reply. For `decide` and `step`, the verdict of a
///   machine and its handle, `holds` or `fails` only with a certificate that
///   the checker replays; for `checkpoint`, the text of an undecided machine
///   and its plan; for `restore`, a new machine from such text, validated
///   again; for `report`, the quanta, the obligations and the certificate steps
///   of a machine. A decline when the payload is not what `Reals` declares, or
///   when a check of the operation fails; one line on `console`'s standard
///   error names the cause first. Nothing for any other interface.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the exemplar admits the square root of two and encloses
///   it at `2^-64`; text that is not hexadecimal, a forged plan, an unknown
///   handle and a precision past the quota are each declined with their cause
///   on standard error. `sqrt 2 < 3/2` holds, two boundary comparisons stop by
///   name, and a checkpoint after one quantum resumes to the uninterrupted
///   verdict.
/// - witness: `tests::run::a_script_encloses_the_square_root_of_two_5700`
/// - witness: `tests::run::a_script_decides_comparisons_through_reals_5703`
#[spec(
    captures: [real = request.signature.name().as_ref() == REALS],
    ensures: |ret| ret.is_none() != real,
)]
pub(super) fn served<Abort>(
    reals: &mut Reals,
    console: &mut dyn Console,
    request: HostRequest<'_>,
    values: &mut HostValues<'_>,
) -> Option<HostReply<Abort>>
{
    if request.signature.name().as_ref() != REALS {
        return None;
    }
    let answered = asked(request.operation, request.payload, values)
        .and_then(|asked| reals.answer(asked))
        .and_then(|answer| reply(answer, values).ok_or(Declined::Store));
    Some(match answered {
        Ok(reply) => HostReply::Resume(reply),
        Err(declined) => {
            let line = format!("{REALS}.{}: {declined}", request.operation.as_ref());
            match console.eprint(Line::from(line.as_str())) {
                Printed::Written | Printed::Failed => {},
            }
            HostReply::Decline
        },
    })
}

impl Reals
{
    /// Answer `asked` over the plans and the machines of the run.
    ///
    /// # Specification
    /// trivial.
    fn answer(
        &mut self,
        asked: Asked<'_>,
    ) -> Result<Answered, Declined>
    {
        match asked {
            Asked::Admit(text) => self.admit(text).map(Answered::Plan),
            Asked::Enclose { handle, width } => self
                .enclose(handle, width)
                .map(|(lower, upper)| Answered::Enclosure(lower, upper)),
            Asked::Decide { handle, budget } => {
                let plan = self
                    .plans
                    .get(handle.0)
                    .map(Rc::clone)
                    .ok_or(Declined::Unknown)?;
                self.machines
                    .decide(plan, budget)
                    .map(|(verdict, machine)| Answered::Verdict(verdict, machine))
            },
            Asked::Step(machine) => self
                .machines
                .step(machine)
                .map(|(verdict, machine)| Answered::Verdict(verdict, machine)),
            Asked::Checkpoint(machine) => self
                .machines
                .checkpoint(machine)
                .map(|bytes| Answered::Text(lowercase(&bytes))),
            Asked::Restore(text) => {
                let bytes = hexadecimal(text).ok_or(Declined::Hexadecimal)?;
                self.machines.restore(&bytes).map(Answered::Machine)
            },
            Asked::Report(machine) => self.machines.report(machine).map(Answered::Counters),
        }
    }

    /// Validate the plan that `text` spells and hold it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the handle of the plan, the place where the table now holds
    ///   it; the table holds no plan that fails validation.
    /// - fails: a full table, text that is not lowercase hexadecimal, and a
    ///   plan that the validation pass refuses, each with the table unchanged.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Declined::Full`], [`Declined::Hexadecimal`] or
    /// [`Declined::Refused`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`served`].
    /// - witness: `tests::run::a_script_encloses_the_square_root_of_two_5700`
    #[spec(
        captures: [before = self.plans.len()],
        ensures: |ret| ret.as_ref().map_or(self.plans.len() == before, |&handle| handle.0 == before && self.plans.len() == before.saturating_add(1)),
    )]
    fn admit(
        &mut self,
        text: &StringLiteral,
    ) -> Result<Handle, Declined>
    {
        if self.plans.len() >= PLANS {
            return Err(Declined::Full);
        }
        let bytes = hexadecimal(text).ok_or(Declined::Hexadecimal)?;
        let plan = validate(
            EncodedPlan::from(bytes.0.as_slice()),
            &Quotas::default(),
            &evidence(),
        )
        .map_err(Declined::Refused)?;
        let handle = Handle(self.plans.len());
        self.plans.push(Rc::new(plan));
        Ok(handle)
    }

    /// The two ends of a certified enclosure of the root of the plan at
    /// `handle`, no wider than `2^width`.
    ///
    /// # Specification
    /// - requires: `width` from `-PRECISION` to zero.
    /// - ensures: the lower end and the upper end of the enclosure that the
    ///   checker replays from the certificate of the machine, the conclusion
    ///   about the root at the width asked.
    /// - fails: a handle that names no plan, a root that is no real, a run of
    ///   the machine that stops short, and a certificate that the checker
    ///   refuses or that concludes another judgement.
    /// - panics: none.
    /// - executable: none — the clause speaks of the machine's certificate and
    ///   its replay, which the function makes.
    ///
    /// # Errors
    /// [`Declined::Unknown`], [`Declined::Proposition`],
    /// [`Declined::Unsettled`], [`Declined::Replay`] or
    /// [`Declined::Mismatch`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`served`].
    /// - witness: `tests::run::a_script_encloses_the_square_root_of_two_5700`
    fn enclose(
        &self,
        handle: Handle,
        width: Exponent,
    ) -> Result<(String, String), Declined>
    {
        let plan: &ValidatedPlan = self
            .plans
            .get(handle.0)
            .map(Rc::as_ref)
            .ok_or(Declined::Unknown)?;
        let obligation =
            Obligation::new(plan, plan.plan().root().node(), Demand::Encloses { width })
                .ok()
                .ok_or(Declined::Proposition)?;
        let quotas = CheckerQuotas::default();
        let mut machine = Dovetail::new(plan, [obligation], Quantum::from(NonZeroU32::MAX), quotas);
        let report = machine.run(Budget::from(STEPS), Rounds::from(1_u64), || false);
        let stopped = match report.outcome(Position::from(0_usize)) {
            Some(Outcome::Certified(certificate)) => Ok(certificate),
            Some(Outcome::Pending) | None => Err(Stopped::Pending),
            Some(Outcome::Exhausted) => Err(Stopped::Exhausted),
            Some(Outcome::Cancelled) => Err(Stopped::Cancelled),
            Some(Outcome::Suspended(reason)) => Err(Stopped::Suspended(reason)),
        };
        let certificate = stopped.map_err(Declined::Unsettled)?;
        let checked = check(plan, certificate, &quotas).map_err(Declined::Replay)?;
        match obligation.answered_by(checked.conclusion()) {
            Answer::Answers => {},
            Answer::Misses => return Err(Declined::Mismatch),
        }
        match *checked.conclusion() {
            Conclusion::Encloses { ref interval, .. } => {
                match (&interval.lower().endpoint, &interval.upper().endpoint) {
                    (&Endpoint::Finite(ref lower), &Endpoint::Finite(ref upper)) => {
                        Ok((spelled(lower), spelled(upper)))
                    },
                    (
                        &(Endpoint::NegInf | Endpoint::Finite(_) | Endpoint::PosInf),
                        &(Endpoint::NegInf | Endpoint::Finite(_) | Endpoint::PosInf),
                    ) => Err(Declined::Mismatch),
                }
            },
            Conclusion::Holds { .. } | Conclusion::Fails { .. } => Err(Declined::Mismatch),
        }
    }
}

/// The evidence that a plan may reference: the laws of the registered cut of
/// stage A at the reference zero, and the overtness and the compactness of an
/// interval domain at one and two. The bounded quantifiers of stage C name
/// the last two.
///
/// # Specification
/// trivial.
fn evidence() -> EvidenceTable
{
    let mut table = EvidenceTable::new();
    for (reference, judgement) in [
        (0_u32, Judgement::CutLaws),
        (1, Judgement::Overt),
        (2, Judgement::Compact),
    ] {
        // A fresh table holds no judgement that a registration conflicts
        // with, and a table without one refuses each plan that names it, so
        // neither answer admits more.
        let _conflict = table.register(Evidence::from(reference), judgement);
    }
    table
}

/// `value` spelled `<mantissa>p<exponent>`, for `mantissa · 2^exponent`.
///
/// # Specification
/// trivial.
fn spelled(value: &Dyadic) -> String
{
    format!("{}p{}", value.mantissa(), i32::from(value.exponent()))
}

/// The bytes that `text` spells in lowercase hexadecimal, two digits a byte.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the byte string whose digits, each pair high first, are `text`;
///   nothing for text of odd length or with a character other than `0`–`9` and
///   `a`–`f`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the plan of the exemplar, and text with a character that
///   is not a digit.
/// - witness: `tests::run::a_script_encloses_the_square_root_of_two_5700`
#[spec(ensures: |ret| ret.as_ref().is_none_or(|bytes| bytes.0.len().checked_mul(2) == Some(AsRef::<str>::as_ref(text).len())))]
fn hexadecimal(text: &StringLiteral) -> Option<Decoded>
{
    let text: &str = text.as_ref();
    let (pairs, odd) = text.as_bytes().as_chunks::<2>();
    if !odd.is_empty() {
        return None;
    }
    let nibble = |digit: u8| match digit {
        b'0' ..= b'9' => digit.checked_sub(b'0'),
        b'a' ..= b'f' => digit.checked_sub(b'a')?.checked_add(10),
        _ => None,
    };
    let mut bytes = Vec::with_capacity(pairs.len());
    for &[high, low] in pairs {
        bytes.push(nibble(high)?.checked_shl(4)? | nibble(low)?);
    }
    Some(Decoded(bytes))
}

/// `bytes` spelled in lowercase hexadecimal, two digits a byte, the high digit
/// first: the text that [`hexadecimal`] reads back.
///
/// # Specification
/// trivial.
fn lowercase(bytes: &Decoded) -> String
{
    bytes
        .0
        .iter()
        .flat_map(|&byte| [byte.checked_shr(4).unwrap_or(0), byte & 0x0f])
        .filter_map(|nibble| char::from_digit(u32::from(nibble), 16))
        .collect()
}

/// What `operation` asks of the plans and the machines, its payload `payload`
/// read out of `values`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `admit` and `restore` with their text, `enclose` with its handle
///   and the width that its precision bounds, `decide` with its handle and its
///   budget, and `step`, `checkpoint` and `report` with the handle of their
///   machine.
/// - fails: a payload that is not what `Reals` declares, or an operation that
///   `Reals` does not declare; a handle below zero or past the places of a
///   table; a precision below zero or past [`PRECISION`]; and a budget below
///   zero or past [`QUANTA`].
/// - panics: none.
/// - executable: none — the clause restates the reading of the payload.
///
/// # Errors
/// [`Declined::Payload`], [`Declined::Unknown`], [`Declined::NoMachine`],
/// [`Declined::Precision`] or [`Declined::Quanta`].
///
/// # Adequacy
/// - hypothesis: L3 — as [`served`].
/// - witness: `tests::run::a_script_encloses_the_square_root_of_two_5700`
/// - witness: `tests::run::a_script_decides_comparisons_through_reals_5703`
fn asked<'values>(
    operation: &OperationName,
    payload: HeapValueId,
    values: &'values HostValues<'_>,
) -> Result<Asked<'values>, Declined>
{
    let text = move || match values.value(payload) {
        Some(&HeapValue::Literal(Literal::Text(ref text))) => Ok(text),
        Some(_) | None => Err(Declined::Payload),
    };
    let pair = move || match values.value(payload) {
        Some(&HeapValue::Constructed {
            tag: ConstructorTag::Tuple(ProducerArity::TWO),
            ref fields,
        }) => fields
            .first()
            .copied()
            .zip(fields.get(1).copied())
            .ok_or(Declined::Payload),
        Some(_) | None => Err(Declined::Payload),
    };
    let plan = move |value: HeapValueId| {
        natural(values, value)?
            .and_then(|digits| digits.as_ref().parse::<usize>().ok())
            .map(Handle)
            .ok_or(Declined::Unknown)
    };
    let machine = move |value: HeapValueId| {
        natural(values, value)?
            .and_then(|digits| digits.as_ref().parse::<usize>().ok())
            .map(MachineHandle)
            .ok_or(Declined::NoMachine)
    };
    match operation.as_ref() {
        ADMIT => text().map(Asked::Admit),
        RESTORE => text().map(Asked::Restore),
        ENCLOSE => {
            let (handle, precision) = pair()?;
            let handle = plan(handle)?;
            let width = natural(values, precision)
                .ok()
                .flatten()
                .and_then(|digits| digits.as_ref().parse::<i32>().ok())
                .filter(|&precision| precision <= PRECISION)
                .map(|precision| Exponent::from(precision.saturating_neg()))
                .ok_or(Declined::Precision)?;
            Ok(Asked::Enclose { handle, width })
        },
        DECIDE => {
            let (handle, budget) = pair()?;
            let handle = plan(handle)?;
            let budget = natural(values, budget)
                .ok()
                .flatten()
                .and_then(|digits| digits.as_ref().parse::<u64>().ok())
                .filter(|&quanta| quanta <= QUANTA)
                .map(Quanta)
                .ok_or(Declined::Quanta)?;
            Ok(Asked::Decide { handle, budget })
        },
        STEP => machine(payload).map(Asked::Step),
        CHECKPOINT => machine(payload).map(Asked::Checkpoint),
        REPORT => machine(payload).map(Asked::Report),
        _ => Err(Declined::Payload),
    }
}

/// The magnitude of the integer that `value` holds, or nothing for an integer
/// below zero.
///
/// # Specification
/// trivial.
fn natural<'values>(
    values: &'values HostValues<'_>,
    value: HeapValueId,
) -> Result<Option<&'values Magnitude>, Declined>
{
    match values.value(value) {
        Some(&HeapValue::Literal(Literal::Integer(ref integer))) => match integer.sign() {
            Sign::NonNegative => Ok(Some(integer.magnitude())),
            Sign::Negative => Ok(None),
        },
        Some(_) | None => Err(Declined::Payload),
    }
}

/// `answer` allocated in `values`: a handle as an integer, an enclosure as a
/// pair of strings, a verdict as its name and the handle of its machine, a
/// checkpoint as its text, and the counters as a list of integers.
///
/// # Specification
/// trivial.
fn reply(
    answer: Answered,
    values: &mut HostValues<'_>,
) -> Option<HeapValueId>
{
    match answer {
        Answered::Plan(handle) => integer(values, handle.0.to_string()),
        Answered::Machine(handle) => integer(values, handle.0.to_string()),
        Answered::Enclosure(lower, upper) => {
            let lower = text(values, lower)?;
            let upper = text(values, upper)?;
            pair(values, [lower, upper])
        },
        Answered::Verdict(verdict, handle) => {
            let name = text(values, verdict.to_string())?;
            let handle = integer(values, handle.0.to_string())?;
            pair(values, [name, handle])
        },
        Answered::Text(spelled) => text(values, spelled),
        Answered::Counters(counters) => {
            let mut list = values
                .allocate(HeapValue::Constructed {
                    tag: ConstructorTag::ListNil,
                    fields: Box::new([]),
                })
                .ok()?;
            for count in [
                counters.certificate.to_string(),
                counters.obligations.to_string(),
                counters.quanta.to_string(),
            ] {
                let head = integer(values, count)?;
                list = values
                    .allocate(HeapValue::Constructed {
                        tag: ConstructorTag::ListCons,
                        fields: Box::new([head, list]),
                    })
                    .ok()?;
            }
            Some(list)
        },
    }
}

/// The non-negative integer that `digits` spell, allocated in `values`.
///
/// # Specification
/// trivial.
fn integer(
    values: &mut HostValues<'_>,
    digits: String,
) -> Option<HeapValueId>
{
    let magnitude = Magnitude::from_decimal_text(digits)?;
    values
        .allocate(HeapValue::Literal(Literal::Integer(IntegerLiteral::new(
            Sign::NonNegative,
            magnitude,
        ))))
        .ok()
}

/// The string `spelled`, allocated in `values`.
///
/// # Specification
/// trivial.
fn text(
    values: &mut HostValues<'_>,
    spelled: String,
) -> Option<HeapValueId>
{
    values
        .allocate(HeapValue::Literal(Literal::Text(StringLiteral::new(
            spelled,
        ))))
        .ok()
}

/// The pair of `fields`, allocated in `values`.
///
/// # Specification
/// trivial.
fn pair(
    values: &mut HostValues<'_>,
    fields: [HeapValueId; 2],
) -> Option<HeapValueId>
{
    values
        .allocate(HeapValue::Constructed {
            tag: ConstructorTag::Tuple(ProducerArity::TWO),
            fields: Box::new(fields),
        })
        .ok()
}
