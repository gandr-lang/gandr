//! Running a lowered command: the tier the policy picks, the content cache
//! native code is served from, the regions a run uses, and the outcome moved
//! into the caller's store.
//!
//! A run lowers its command every time — the lowered function is the cache
//! key, compared by value — and either serves the function's emitted code
//! from the process's cache, emitting it on a miss, or builds the executor's
//! program. Both run over the calling thread's heap and frame regions, each
//! allocated at its bound once per thread and committed page by page as runs
//! touch it; a run that would pass a bound declines exhausted. The
//! alternative was a small region doubled and the run repeated from its
//! start, which offers a host handler its requests a second time; the bound
//! costs address space only. The choice reverses if a workload needs more
//! than a bound holds, when the bound becomes the caller's to set.

#[cfg(gandr_patcher)]
use alloc::sync::Arc;
use core::cell::RefCell;

use gandr_core_sequent::CommandArena;
use gandr_core_sequent::CommandId;
use gandr_core_sequent::Definitions;
use gandr_core_sequent::DestructorTag;
use gandr_core_sequent::HeapValueId;
use gandr_core_sequent::Outcome;
use gandr_core_sequent::Store;
use gandr_core_sequent::Stuck;
use gandr_kernel_term::Component;
use gandr_runtime_stencils::Fuel;
use gandr_runtime_stencils::Observed;
use gandr_runtime_stencils::Runtime;
use gandr_runtime_stencils::Status;
use gandr_runtime_stencils::Word;

use crate::executor::Program;
use crate::function::Unbound;
use crate::host;
use crate::host::Calls;
use crate::host::Codes;
use crate::host::Parts;
use crate::host::Refused;
use crate::lower::Form;
use crate::lower::Lowered;
use crate::lower::lower;
use crate::lower::lower_unfused;
#[cfg(gandr_patcher)]
use crate::native::EmitRefusal;
#[cfg(gandr_patcher)]
use crate::native::Emitted;
#[cfg(gandr_patcher)]
use crate::native::Native;
use crate::seam::Adapter;
use crate::seam::HostHandler;
use crate::seam::HostOutcome;
use crate::seam::Offer;
use crate::transfer::Sites;
use crate::transfer::TransferRefusal;

/// The environment variable the policy is read from.
pub const POLICY_VARIABLE: &str = "GANDR_NATIVE";

/// When a run takes native code.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub enum Policy
{
    /// Emit on a function's first run and serve the cache after: native
    /// wherever a patcher exists.
    #[default]
    Always,
    /// Never emit: every run takes the portable executor.
    Never,
    /// Serve a function the cache already holds; take the executor on a
    /// miss, emitting nothing.
    Cached,
}

impl Policy
{
    /// The policy `GANDR_NATIVE` names: `always`, `never` or `cached`;
    /// [`Policy::Always`] when the variable is unset or names none of them.
    ///
    /// # Specification
    /// - ensures: the spelling decides, case-sensitively; anything else is the
    ///   default.
    /// - executable: none — the spellings are [`From<&str>`]'s, which the
    ///   witness reads directly; the environment is the process's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each spelling and an unknown one select their policy.
    /// - witness: `run::tests::the_policy_reads_its_three_spellings`
    #[inline]
    #[must_use]
    pub fn from_environment() -> Self
    {
        Self::from(std::env::var(POLICY_VARIABLE).ok().as_deref().unwrap_or(""))
    }
}

impl From<&str> for Policy
{
    /// The policy a spelling names: `always`, `never` or `cached`, the
    /// default for anything else.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(spelling: &str) -> Self
    {
        match spelling {
            "never" => Self::Never,
            "cached" => Self::Cached,
            _ => Self::Always,
        }
    }
}

/// Which code a run takes.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Tier
{
    /// Emitted native code, served from the cache.
    Native,
    /// The portable executor.
    Executor,
}

/// Why a run gave no outcome.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Declined
{
    /// The lowering refused a form.
    Lowering(Form),
    /// The host has no patcher, and the native tier was asked for.
    NoPatcher,
    /// Emission refused the function.
    #[cfg(gandr_patcher)]
    Emission(EmitRefusal),
    /// A label of the function is unbound.
    Unbound,
    /// The policy serves only cached code and the cache misses.
    Uncached,
    /// The run stopped stuck where nothing named why: a host call refused
    /// operands no well-formed command gives it.
    Stuck,
    /// The run spent its fuel, or a region past its bound.
    Exhausted(Status),
    /// The answer, or a value the run stopped at or offered, could not be
    /// moved into the store.
    Transfer(TransferRefusal),
    /// The host resumed with a value its store does not hold, or one a run
    /// cannot hold: code the host built rather than a value the run moved out.
    Reply(HeapValueId),
}

impl From<Form> for Declined
{
    /// The lowering's refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(form: Form) -> Self
    {
        Self::Lowering(form)
    }
}

impl From<Unbound> for Declined
{
    /// An unbound label.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(_unbound: Unbound) -> Self
    {
        Self::Unbound
    }
}

impl From<TransferRefusal> for Declined
{
    /// The transfer's refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(refusal: TransferRefusal) -> Self
    {
        Self::Transfer(refusal)
    }
}

impl core::fmt::Display for Declined
{
    /// Says why the run gave no outcome, in a line.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        match *self {
            Self::Lowering(form) => write!(f, "the lowering refused {form}"),
            Self::NoPatcher => f.write_str("the host has no patcher for native code"),
            #[cfg(gandr_patcher)]
            Self::Emission(_) => f.write_str("native emission refused the function"),
            Self::Unbound => f.write_str("a label of the function is unbound"),
            Self::Uncached => f.write_str("the cache holds no code for the function"),
            Self::Stuck => f.write_str("the run stopped stuck where nothing named why"),
            Self::Exhausted(Status::FuelExhausted) => f.write_str("the run spent its budget"),
            Self::Exhausted(Status::HeapExhausted) => {
                f.write_str("the heap region passed its bound")
            },
            Self::Exhausted(Status::FramesExhausted) => {
                f.write_str("the frame region passed its bound")
            },
            Self::Exhausted(
                Status::Running | Status::Halted | Status::Unmatched | Status::Stuck,
            ) => f.write_str("the run exited with a status no run returns"),
            Self::Transfer(_) => f.write_str("a value could not be moved into the store"),
            Self::Reply(value) => {
                write!(
                    f,
                    "the host resumed with {value}, which the run cannot hold"
                )
            },
        }
    }
}

/// The process's emitted code, by the function it runs.
#[cfg(gandr_patcher)]
#[derive(Debug, Default)]
struct Cache
{
    /// The regions the code lives in.
    native: Native,
    /// Each function's emitted code.
    entries: std::collections::HashMap<crate::function::Function, Arc<Emitted>>,
}

/// The process's cache. A run-count gate before emission would be a no-op
/// here: a function is lowered from its source each process, so the first
/// run is the only run the gate could skip. The cache that serves code
/// across processes is the persistent, content-keyed one.
#[cfg(gandr_patcher)]
static CACHE: std::sync::LazyLock<std::sync::Mutex<Cache>> =
    std::sync::LazyLock::new(|| std::sync::Mutex::new(Cache::default()));

/// The policy, read once per process.
static POLICY: std::sync::LazyLock<Policy> = std::sync::LazyLock::new(Policy::from_environment);

/// The regions a run uses, per thread, each allocated at its bound and
/// committed as a run first touches it.
#[derive(Debug)]
struct Buffers
{
    /// The heap region: capacity only, every word written before it is read.
    heap: Vec<Word>,
    /// The frame region: capacity only, the sentinel frame written in its
    /// first two words.
    frames: Vec<Word>,
    /// The entry window.
    window: Vec<Word>,
}

/// The heap region's bound, in words: past it the run declines.
const HEAP_BOUND: usize = 1 << 25;
/// The frame region's bound, in words: past it the run declines.
const FRAME_BOUND: usize = 1 << 23;

std::thread_local! {
    /// The calling thread's regions.
    static BUFFERS: RefCell<Buffers> = RefCell::new(Buffers {
        heap: Vec::with_capacity(HEAP_BOUND),
        frames: Vec::with_capacity(FRAME_BOUND),
        window: Vec::new(),
    });
}

/// The code a run enters.
#[derive(Clone, Copy, Debug)]
enum Code<'program>
{
    /// Emitted code: its entry and its region's halt.
    #[cfg(gandr_patcher)]
    Native(Word, Word),
    /// An executor program.
    Executor(&'program Program),
}

/// How a run ended, the host's abort apart.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Ran
{
    /// The run halted or stopped stuck.
    Ended(Outcome),
    /// The host stopped the run.
    Aborted,
}

impl Ran
{
    /// The outcome of a run with no host, which nothing aborts.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Declined::Stuck`] for an abort, which no run without a host makes.
    fn hostless(self) -> Result<Outcome, Declined>
    {
        match self {
            Self::Ended(outcome) => Ok(outcome),
            Self::Aborted => Err(Declined::Stuck),
        }
    }
}

/// Run `root` under the process's policy and move its outcome into `store`.
///
/// # Specification
/// - ensures: as [`evaluate_on`], on the tier the policy picks: native under
///   [`Policy::Always`] where a patcher exists and emits the function, the
///   executor under [`Policy::Never`], on a miss under [`Policy::Cached`], and
///   wherever native code is not to be had.
/// - executable: none — the tiers' agreement is the differential's to show; a
///   postcondition would run every command twice.
///
/// # Errors
/// As [`evaluate_on`], but never [`Declined::NoPatcher`] or an emission
/// refusal: the executor runs the command instead.
///
/// # Adequacy
/// - hypothesis: L2 — every named program runs through this entry and is
///   compared with each tier's outcome; the policy's spellings are witnessed
///   apart.
/// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
/// - witness: `run::tests::the_policy_reads_its_three_spellings`
#[inline]
pub fn evaluate(
    arena: &CommandArena,
    definitions: &Definitions,
    root: CommandId,
    fuel: Fuel,
    store: &mut Store,
) -> Result<Outcome, Declined>
{
    let lowered = lower(arena, definitions, root)?;
    by_policy(&lowered, arena, fuel, store, None)?.hostless()
}

/// Run `root` on `tier` with `fuel` code-word jumps and move its outcome into
/// `store`; an operation no handler of the run claims stops it stuck.
///
/// # Specification
/// - requires: every constant `root` reaches is defined in `definitions`.
/// - ensures: on success how the run ended: the value it halted with, or the
///   reason it stopped stuck, every value either names moved into the store as
///   its readback reads it.
/// - executable: none — the tiers' agreement is the differential's to show; a
///   postcondition would run every command twice.
///
/// # Errors
/// [`Declined`] naming why the run gave no outcome: a form the lowering
/// refuses, a spent budget, a region past its bound.
///
/// # Adequacy
/// - hypothesis: L2 — the named programs run on both tiers and their outcomes
///   are compared value by value, and with the outcome each states.
/// - witness: `tests::agreement::the_named_programs_agree_on_both_executors`
#[inline]
pub fn evaluate_on(
    tier: Tier,
    arena: &CommandArena,
    definitions: &Definitions,
    root: CommandId,
    fuel: Fuel,
    store: &mut Store,
) -> Result<Outcome, Declined>
{
    let lowered = lower(arena, definitions, root)?;
    on_tier(tier, &lowered, arena, fuel, store, None)?.hostless()
}

/// As [`evaluate_on`], the command's unfused lowering run: every instruction
/// its own dispatch, the reference a fused function answers to.
///
/// # Specification
/// - requires: as [`evaluate_on`].
/// - ensures: as [`evaluate_on`], over [`lower_unfused`]'s function.
/// - executable: none — as [`evaluate_on`].
///
/// # Errors
/// As [`evaluate_on`].
///
/// # Adequacy
/// - hypothesis: L2 — every named, generated and corpus program runs unfused
///   beside its fused function, with equal outcomes.
/// - witness: `tests::agreement::a_fused_program_answers_what_its_unfused_lowering_answers`
#[inline]
pub fn evaluate_unfused_on(
    tier: Tier,
    arena: &CommandArena,
    definitions: &Definitions,
    root: CommandId,
    fuel: Fuel,
    store: &mut Store,
) -> Result<Outcome, Declined>
{
    let lowered = lower_unfused(arena, definitions, root)?;
    on_tier(tier, &lowered, arena, fuel, store, None)?.hostless()
}

/// As [`evaluate`], an operation no handler of the run claims offered to
/// `host`.
///
/// # Specification
/// - ensures: as [`evaluate_on_with_host`], on the tier the policy picks as
///   [`evaluate`] picks it.
/// - executable: none — as [`evaluate`].
///
/// # Errors
/// As [`evaluate_on_with_host`], but never [`Declined::NoPatcher`] or an
/// emission refusal.
///
/// # Adequacy
/// - hypothesis: L3 — a host reply runs on through the policy's tier as it does
///   on each tier alone.
/// - witness: `tests::seam::a_host_reply_flows_into_the_rest_of_the_run`
#[inline]
pub fn evaluate_with_host<Host>(
    arena: &CommandArena,
    definitions: &Definitions,
    root: CommandId,
    (fuel, store): (Fuel, &mut Store),
    host: &mut Host,
) -> Result<HostOutcome<Host::Abort>, Declined>
where
    Host: HostHandler,
{
    let lowered = lower(arena, definitions, root)?;
    let mut adapter = Adapter {
        host,
        aborted: None,
    };
    let ran = by_policy(&lowered, arena, fuel, store, Some(&mut adapter))?;
    hosted(ran, adapter)
}

/// As [`evaluate_on`], an operation no handler of the run claims offered to
/// `host`.
///
/// # Specification
/// - requires: as [`evaluate_on`].
/// - ensures: as [`evaluate_on`], each unclaimed operation offered to the host
///   once, its payload moved into the store: a reply continues the operation's
///   continuation, a decline leaves the run stuck at the operation, and an
///   abort ends the run with the host's result.
/// - executable: none — as [`evaluate_on`].
///
/// # Errors
/// As [`evaluate_on`], and [`Declined::Reply`] for a reply the run cannot
/// hold.
///
/// # Adequacy
/// - hypothesis: L3 — scripted hosts that resume, abort and decline, offered
///   operations claimed and unclaimed by the run's handlers, on each tier.
/// - witness: `tests::seam::a_host_resumes_a_single_unhandled_perform`
/// - witness: `tests::seam::a_host_abort_never_resumes_and_a_missing_reply_declines`
#[inline]
pub fn evaluate_on_with_host<Host>(
    tier: Tier,
    (arena, definitions, root): (&CommandArena, &Definitions, CommandId),
    (fuel, store): (Fuel, &mut Store),
    host: &mut Host,
) -> Result<HostOutcome<Host::Abort>, Declined>
where
    Host: HostHandler,
{
    let lowered = lower(arena, definitions, root)?;
    let mut adapter = Adapter {
        host,
        aborted: None,
    };
    let ran = on_tier(tier, &lowered, arena, fuel, store, Some(&mut adapter))?;
    hosted(ran, adapter)
}

/// A hosted run's outcome: an abort carries the result the host kept.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`Declined::Stuck`] for an abort the host kept no result for, which no
/// adapter makes.
fn hosted<Host>(
    ran: Ran,
    adapter: Adapter<'_, Host>,
) -> Result<HostOutcome<Host::Abort>, Declined>
where
    Host: HostHandler,
{
    match ran {
        Ran::Ended(outcome) => Ok(HostOutcome::Completed(outcome)),
        Ran::Aborted => adapter
            .aborted
            .map(HostOutcome::Aborted)
            .ok_or(Declined::Stuck),
    }
}

/// Run `lowered` on the tier the policy picks, the executor wherever native
/// code is not to be had.
///
/// # Specification
/// trivial.
///
/// # Errors
/// As [`evaluate`].
fn by_policy(
    lowered: &Lowered,
    arena: &CommandArena,
    fuel: Fuel,
    store: &mut Store,
    mut offer: Option<&mut (dyn Offer + '_)>,
) -> Result<Ran, Declined>
{
    match *POLICY {
        Policy::Always => match run_native(lowered, arena, fuel, store, offer.as_deref_mut()) {
            Err(Declined::NoPatcher) => run_executor(lowered, arena, fuel, store, offer),
            #[cfg(gandr_patcher)]
            Err(Declined::Emission(_)) => run_executor(lowered, arena, fuel, store, offer),
            ran => ran,
        },
        Policy::Never => run_executor(lowered, arena, fuel, store, offer),
        Policy::Cached => run_cached(lowered, arena, fuel, store, offer),
    }
}

/// Run `lowered` on `tier`.
///
/// # Specification
/// trivial.
///
/// # Errors
/// As [`evaluate_on`].
fn on_tier(
    tier: Tier,
    lowered: &Lowered,
    arena: &CommandArena,
    fuel: Fuel,
    store: &mut Store,
    offer: Option<&mut (dyn Offer + '_)>,
) -> Result<Ran, Declined>
{
    match tier {
        Tier::Native => run_native(lowered, arena, fuel, store, offer),
        Tier::Executor => run_executor(lowered, arena, fuel, store, offer),
    }
}

/// Run on the executor.
///
/// # Specification
/// trivial.
///
/// # Errors
/// As [`evaluate_on`].
fn run_executor(
    lowered: &Lowered,
    arena: &CommandArena,
    fuel: Fuel,
    store: &mut Store,
    offer: Option<&mut (dyn Offer + '_)>,
) -> Result<Ran, Declined>
{
    let program = Program::build(&lowered.function)?;
    let codes = Codes::Executor(&program, &lowered.function);
    let sites = Sites::new(lowered, codes);
    run(
        Code::Executor(&program),
        Parts {
            lowered,
            codes,
            sites: &sites,
            arena,
            store,
            offer,
        },
        fuel,
    )
}

/// Run emitted code, emitting on a miss.
///
/// # Specification
/// trivial.
///
/// # Errors
/// As [`evaluate_on`].
#[cfg(gandr_patcher)]
fn run_native(
    lowered: &Lowered,
    arena: &CommandArena,
    fuel: Fuel,
    store: &mut Store,
    offer: Option<&mut (dyn Offer + '_)>,
) -> Result<Ran, Declined>
{
    let emitted = {
        let mut cache = CACHE
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if let Some(held) = cache.entries.get(&lowered.function) {
            Arc::clone(held)
        }
        else {
            let emitted = Arc::new(
                cache
                    .native
                    .emit(&lowered.function)
                    .map_err(Declined::Emission)?,
            );
            cache
                .entries
                .insert(lowered.function.clone(), Arc::clone(&emitted));
            emitted
        }
    };
    run_emitted(&emitted, lowered, arena, fuel, (store, offer))
}

/// The native tier needs a patcher this host lacks.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`Declined::NoPatcher`], always.
#[cfg(not(gandr_patcher))]
fn run_native(
    lowered: &Lowered,
    arena: &CommandArena,
    fuel: Fuel,
    store: &mut Store,
    offer: Option<&mut (dyn Offer + '_)>,
) -> Result<Ran, Declined>
{
    let _ = (lowered, arena, fuel, store, offer);
    Err(Declined::NoPatcher)
}

/// Serve cached code, or take the executor on a miss.
///
/// # Specification
/// trivial.
///
/// # Errors
/// As [`evaluate_on`].
fn run_cached(
    lowered: &Lowered,
    arena: &CommandArena,
    fuel: Fuel,
    store: &mut Store,
    offer: Option<&mut (dyn Offer + '_)>,
) -> Result<Ran, Declined>
{
    #[cfg(gandr_patcher)]
    {
        let held = CACHE
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .entries
            .get(&lowered.function)
            .map(Arc::clone);
        if let Some(emitted) = held {
            return run_emitted(&emitted, lowered, arena, fuel, (store, offer));
        }
    }
    run_executor(lowered, arena, fuel, store, offer)
}

/// Run code the cache served.
///
/// # Specification
/// trivial.
///
/// # Errors
/// As [`evaluate_on`].
#[cfg(gandr_patcher)]
fn run_emitted(
    emitted: &Emitted,
    lowered: &Lowered,
    arena: &CommandArena,
    fuel: Fuel,
    (store, offer): (&mut Store, Option<&mut (dyn Offer + '_)>),
) -> Result<Ran, Declined>
{
    let codes = Codes::Native {
        labels: &emitted.labels,
        stubs: &emitted.stubs,
    };
    let sites = Sites::new(lowered, codes);
    run(
        Code::Native(emitted.entry, emitted.halt),
        Parts {
            lowered,
            codes,
            sites: &sites,
            arena,
            store,
            offer,
        },
        fuel,
    )
}

/// Run `code` once over the calling thread's regions and move how it ended
/// into `parts`' store.
///
/// # Specification
/// trivial.
///
/// # Errors
/// As [`evaluate_on_with_host`].
fn run(
    code: Code<'_>,
    parts: Parts<'_, '_>,
    fuel: Fuel,
) -> Result<Ran, Declined>
{
    let lowered = parts.lowered;
    BUFFERS.with_borrow_mut(|buffers| {
        buffers.window.clear();
        buffers
            .window
            .resize(lowered.function.slots().0.max(1), Word::ZERO);
        let halt = match code {
            #[cfg(gandr_patcher)]
            Code::Native(_, halt) => halt,
            Code::Executor(program) => program.halt(),
        };
        let table = buffers.heap.as_mut_ptr();
        let heap_limit = table.wrapping_add(buffers.heap.capacity());
        // The constant table sits at the heap's base, every word zero: no
        // constant is unfolded yet.
        let constants = lowered.globals.len();
        if constants > buffers.heap.capacity() {
            return Err(Declined::Exhausted(Status::HeapExhausted));
        }
        // SAFETY: the heap region's capacity holds the table's words.
        unsafe {
            table.write_bytes(0, constants);
        }
        let heap = table.wrapping_add(constants);
        let frames = buffers.frames.as_mut_ptr();
        let frame_limit = frames.wrapping_add(buffers.frames.capacity());
        // SAFETY: the frame region's capacity holds far more than the
        // sentinel's two words.
        unsafe {
            frames.write(halt);
        }
        // SAFETY: as above.
        unsafe {
            frames.wrapping_add(1).write(Word::ZERO);
        }
        let base = frames.wrapping_add(2);
        let window = buffers.window.as_mut_ptr();
        let mut calls = Calls::new(parts);
        let mut runtime = Runtime::new(
            heap,
            heap_limit,
            frame_limit,
            base,
            fuel,
            host::enter,
            Word::from_pointer(&raw mut calls),
        );
        runtime.set_globals(table);
        let answer = match code {
            #[cfg(gandr_patcher)]
            // SAFETY: the entry is a copy the emitter patched in a region the
            // cache keeps mapped; the regions are this thread's, valid up to
            // their limits, the sentinel frame below the base mark, and the
            // window holds the function's slots.
            Code::Native(entry, _) => unsafe {
                gandr_runtime_stencils::enter(entry, &raw mut runtime, heap, base, window)
            },
            // SAFETY: the program was built from this function and lives for
            // the call; the regions are as above.
            Code::Executor(program) => unsafe {
                gandr_runtime_stencils::execute(
                    program.entry(),
                    &raw mut runtime,
                    heap,
                    base,
                    window,
                )
            },
        };
        let refused = calls.refused().cloned();
        // SAFETY: the run exited; its heap and the function's constants are
        // live until this closure returns, and every exit but the regions'
        // and the fuel's returns a value of that heap or zero.
        let mut moved = |word: Word| unsafe { calls.moved(word) };
        let stuck = match runtime.status() {
            Ok(Status::Halted) => return Ok(Ran::Ended(Outcome::Halted(moved(answer)?))),
            Ok(Status::Unmatched) => {
                let arms = lowered
                    .unmatched
                    .get(usize::from(runtime.observed()))
                    .copied()
                    .ok_or(Declined::Stuck)?;
                Stuck::Unmatched {
                    value: moved(answer)?,
                    arms,
                }
            },
            Ok(Status::Stuck) => match refused {
                Some(Refused::PerformNoHandler(at)) => Stuck::PerformNoHandler(at),
                Some(Refused::ShiftNoReset(at)) => Stuck::ShiftNoReset(at),
                Some(Refused::ResumedNonStack { at, value }) => Stuck::ResumedNonStack {
                    at,
                    value: moved(value)?,
                },
                Some(Refused::Primitive(error)) => Stuck::Primitive(error),
                Some(Refused::NonScalar(value)) => Stuck::NonScalar(moved(value)?),
                Some(Refused::Unended(at)) => Stuck::Unended(at),
                Some(Refused::Outside(at)) => Stuck::Outside(at),
                Some(Refused::UndefinedConstant(constant)) => Stuck::UndefinedConstant(constant),
                Some(Refused::CyclicConstant(constant)) => Stuck::CyclicConstant(constant),
                Some(Refused::Aborted) => return Ok(Ran::Aborted),
                Some(Refused::Operands) => return Err(Declined::Stuck),
                Some(Refused::Reply(value)) => return Err(Declined::Reply(value)),
                Some(Refused::Transfer(refusal)) => return Err(Declined::Transfer(refusal)),
                None => {
                    let head = match Observed::try_from(runtime.observed()) {
                        Ok(Observed::Apply) => DestructorTag::Apply,
                        Ok(Observed::Force) => DestructorTag::Force,
                        Ok(Observed::Project(component)) => {
                            DestructorTag::Project(Component::from(usize::from(component)))
                        },
                        Err(_unnamed) => return Err(Declined::Stuck),
                    };
                    Stuck::Unobservable {
                        value: moved(answer)?,
                        head,
                    }
                },
            },
            Ok(status) => return Err(Declined::Exhausted(status)),
            Err(_unknown) => return Err(Declined::Exhausted(Status::Running)),
        };
        Ok(Ran::Ended(Outcome::Stuck(stuck)))
    })
}

#[cfg(test)]
mod tests
{
    use super::Policy;

    /// Each spelling of the variable selects its policy, and anything else
    /// the default: a misspelt `never` emits rather than silently running
    /// slower.
    #[test]
    fn the_policy_reads_its_three_spellings()
    {
        assert_eq!(
            Policy::Always,
            Policy::from("always"),
            "the default's own spelling"
        );
        assert_eq!(Policy::Never, Policy::from("never"), "never emits");
        assert_eq!(Policy::Cached, Policy::from("cached"), "serves hits only");
        assert_eq!(Policy::Always, Policy::from(""), "unset is the default");
        assert_eq!(
            Policy::Always,
            Policy::from("Never"),
            "spellings are case-sensitive"
        );
    }
}
